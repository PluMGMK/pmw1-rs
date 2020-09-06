/*!
  Code for dealing with full PMW1 EXE files, apart from the DOS stub at the beginning.

  A PMW1 EXE is made up of objects, and information about how to load and execute them.
  */

// It seems appropriate to craft I/O errors for this, instead of the overhead of maintaining my own
// error class...
use std::io::{Result,Error,ErrorKind};

use crate::object::Pmw1Object;
use crate::constants::*;

/// A struct representing a PMW1 executable, excluding the DOS stub but including all the objects
/// and metadata.
///
/// Note that you can iterate over the executable's objects, but you can't add or remove them. If
/// you really need to do that, you can create a new executable with all the objects you need in
/// the right order. The same goes if you want to mess with the version metadata.
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct Pmw1Exe {
    version_major:u8,
    version_minor:u8,
    flags:u16,
    entry_object:u32,
    entry_point:u32,
    stack_object:u32,
    stack_pointer:u32,
    
    objects:Vec<Pmw1Object>,
    //relocation_buf:Vec<u8>,
}

impl Pmw1Exe {
    /// Create a new PMW1 executable from its components.
    ///
    /// ## Details:
    /// This function allows you to specify:
    /// * The executable's `objects`, by passing a mutable iterator over [`Pmw1Object`]s.
    /// * The `version` of PMODE/W with which the executable is compatible, as a `(major, minor)`
    /// tuple.
    /// * The object's `flags`, as a 16-bit-string. According to the PMODE/W code documentation,
    /// only the first of these flags was ever used, and it indicates whether or not the executable
    /// is compressed.
    /// * The entry point for the executable, as a tuple `(object_index, offset)`. Remember, the
    /// objects are indexed starting from 1 rather than 0!
    /// * The initial position of the stack pointer in the executable's memory, as a tuple
    /// `(object_index, offset)`. Again, remember that the objects are indexed starting from 1
    /// rather than 0!
    ///
    /// ## Returns:
    /// * This will return a [`std::io::Error`] of kind [`InvalidInput`](ErrorKind::InvalidInput)
    /// if the entry point or stack pointer is specified in an invalid object or at an invalid
    /// offset within its object (i.e. beyond the end).
    pub fn new<I: Iterator<Item = Pmw1Object>>(objects: &mut I, version: (u8, u8), flags: u16, entry_point: (u32, u32), stack_pointer: (u32, u32)) -> Result<Self> {
        let objects = objects.collect::<Vec<_>>();

        // Sanity checks
        if entry_point.0 as usize > objects.len() {
            return Err(Error::new(ErrorKind::InvalidInput, "Entry point is in a non-existent object!"));
        } else if entry_point.1 as usize > objects[entry_point.0 as usize - 1].virtual_size() {
            return Err(Error::new(ErrorKind::InvalidInput, "Entry point is outside the address space of its object!"));
        } else if stack_pointer.0 as usize > objects.len() {
            return Err(Error::new(ErrorKind::InvalidInput, "Stack is in a non-existent object!"));
        } else if stack_pointer.1 as usize > objects[stack_pointer.0 as usize - 1].virtual_size() {
            return Err(Error::new(ErrorKind::InvalidInput, "Stack is outside the address space of its object!"));
        }

        Ok(Pmw1Exe {
            version_major:version.0,
            version_minor:version.1,
            flags:flags,
            entry_object:entry_point.0,
            entry_point:entry_point.1,
            stack_object:stack_pointer.0,
            stack_pointer:stack_pointer.1,
            
            objects:objects,
        })
    }

    /// Interprets a buffer of bytes as a PMW1 executable. This buffer should be read starting from
    /// the end of the DOS stub of an actual PMW1 EXE file.
    pub fn from_bytes(buf: &[u8]) -> Result<Self> {
        if buf[0..4] != b"PMW1"[..] {
            return Err(Error::new(ErrorKind::InvalidData, "Not a PMW1 executable!"));
        }
        if buf.len() < 0x28 {
            return Err(Error::new(ErrorKind::UnexpectedEof, "PMW1 header appears incomplete!"));
        }

        let version_major = buf[4];
        let version_minor = buf[5];

        // Flags are stored in a two-byte word.
        let flags = u16::from_le_bytes([buf[6], buf[7]]);

        // The rest of the header is made of dwords.
        let rem_header = &buf[0x8..0x28];
        let rem_header: Vec<u32> = (0..rem_header.len())
            .step_by(4)
            .map(|i| u32::from_le_bytes([rem_header[i],
                                        rem_header[i+1],
                                        rem_header[i+2],
                                        rem_header[i+3]]))
            .collect();

        // Basic fields
        let entry_object = rem_header[0];
        let entry_point = rem_header[1];
        let stack_object = rem_header[2];
        let stack_pointer = rem_header[3];

        // Stuff to use to make objects and relocations
        let objtable_offset = rem_header[4] as usize;
        let objtable_entries = rem_header[5] as usize;
        let rt_offset = rem_header[6] as usize;
        let data_offset = rem_header[7] as usize;

        // Get the relocation table into a buffer. Can't do any better than that at this point
        // since it may be compressed...
        let relocation_buf = 
            if data_offset < rt_offset {
                return Err(Error::new(ErrorKind::InvalidData, "Invalid PMW1 header – suggests data comes before relocation table!"));
            } else {
                match buf.get(rt_offset..data_offset) {
                    Some(slice) => slice.to_vec(),
                    None => {
                        return Err(Error::new(ErrorKind::InvalidData, "Invalid PMW1 header – suggests relocation table goes beyond the end of the file!"));
                    },
                }
            };

        // Get the data pages into an iterator so we can allocate the data to objects.
        let mut data_pages_buf_iter = 
            if data_offset < 0x28 {
                // If we allowed this to happen, it would mean reading from a section of buf that
                // is also referenced by rem_header – not sure whether that's sound or not, so bail
                // out just in case!
                return Err(Error::new(ErrorKind::InvalidData, "Invalid PMW1 header – suggests data starts inside the header itself!"));
            } else {
                match buf.get(data_offset..) {
                    Some(slice) => slice.iter(),
                    None => {
                        return Err(Error::new(ErrorKind::UnexpectedEof, "Invalid PMW1 header – suggests data starts beyond the end of the file!"));
                    },
                }
            };

        // Now construct the objects...
        let objects = (0..objtable_entries)
            .map(|idx| {
                let table_entry_offset = objtable_offset + idx*PMW1_OBJTABLE_ENTRY_SIZE;
                let table_entry = match buf.get(table_entry_offset..(table_entry_offset+PMW1_OBJTABLE_ENTRY_SIZE)) {
                    Some(entry) => entry,
                    None => return Err(Error::new(ErrorKind::UnexpectedEof, "Incomplete object table")),
                };
                Pmw1Object::from_tabentry_byteslice(&table_entry, &relocation_buf, data_pages_buf_iter.by_ref())
            }).collect::<Result<Vec<_>>>()?;

        match Pmw1Exe::new(&mut objects.into_iter(),
                           (version_major, version_minor),
                           flags,
                           (entry_object, entry_point),
                           (stack_object, stack_pointer)) {
            Ok(exe) => Ok(exe),
            Err(error) => Err(Error::new(ErrorKind::InvalidData, format!("Invalid PMW1 header – {}", error.into_inner().unwrap()))),
        }
    }

    /// Returns the PMODE/W version with which this executable is compatible, as a `(major, minor)`
    /// tuple.
    pub fn pmw_version(&self) -> (u8, u8) {
        (self.version_major, self.version_minor)
    }

    /// Returns this PMW1 executable's `n`th flag, as a [`bool`].
    ///
    /// ## Requirements:
    /// * `n` must be less than 16, since there are only 16 flag bits in total.
    pub fn flag(&self, n:u8) -> Result<bool> {
        if (n >> 4) != 0 {
            Err(Error::new(ErrorKind::InvalidInput, "Trying to read PMW1 executable flag beyond 15"))
        } else {
            Ok((self.flags & (1 << n)) != 0)
        }
    }

    /// Sets this PMW1 executable's `n`th flag according to `val` (1 if `true`, 0 if `false`).
    ///
    /// ## Requirements:
    /// * `n` must be less than 16, since there are only 16 flag bits in total.
    /// * `n` cannot be zero, since the 0th bit represents compression. You have to use
    /// [`compress()`](Pmw1Exe::compress) or [`decompress()`](Pmw1Exe::decompress) to change this
    /// aspect of the executable's state.
    pub fn set_flag(&mut self, n:u8, val:bool) -> Result<()> {
        if (n >> 4) != 0 {
            Err(Error::new(ErrorKind::InvalidInput, "Trying to write PMW1 executable flag beyond 15"))
        } else if n == 0 {
            Err(Error::new(ErrorKind::PermissionDenied, "You can't set the compression flag on a PMW1 executable manually. Use the compress() or decompress() method."))
        } else {
            if val {
                self.flags |= 1 << n;
            } else {
                self.flags &= !(1 << n);
            }
            Ok(())
        }
    }

    /// Returns this PMW1 executable's entry point as a tuple `(object_index, offset)`. Remember, the
    /// objects are indexed starting from 1 rather than 0!
    pub fn entry_point(&self) -> (u32, u32) {
        (self.entry_object, self.entry_point)
    }

    /// Returns a reference to the [object](Pmw1Object) in which this executable's entry point is
    /// located.
    pub fn entry_object(&self) -> &Pmw1Object {
        self.object(self.entry_point().0 as usize).unwrap()
    }

    /// Returns a mutable reference to the [object](Pmw1Object) in which this executable's entry point is
    /// located.
    pub fn entry_object_mut(&mut self) -> &mut Pmw1Object {
        self.object_mut(self.entry_point().0 as usize).unwrap()
    }

    /// Sets the executable's entry point at `offset` in the memory space of the `obj_idx`th
    /// object. Remember, the objects are indexed starting from 1 rather than 0!
    ///
    /// ## Requirements:
    /// * `obj_idx` must refer to a valid object in the executable. Zero is never a valid index.
    /// * `offset` must be within the address space of the object (i.e. less than or equal to
    /// `self.objects(obj_idx as usize).virtual_size()`).
    pub fn set_entry_point(&mut self, obj_idx: u32, offset: u32) -> Result<()> {
        if let Some(obj) = self.object(obj_idx as usize) {
            if offset as usize <= obj.virtual_size() {
                self.entry_object = obj_idx;
                self.entry_point = offset;
                Ok(())
            } else {
                Err(Error::new(ErrorKind::InvalidInput, "Tried to set entry point outside the address space of its object!"))
            }
        } else {
            Err(Error::new(ErrorKind::InvalidInput, "Tried to set entry point in a non-existent object!"))
        }
    }

    /// Returns this PMW1 executable's initial stack pointer as a tuple `(object_index, offset)`.
    /// Remember, the objects are indexed starting from 1 rather than 0!
    pub fn stack_pointer(&self) -> (u32, u32) {
        (self.stack_object, self.stack_pointer)
    }

    /// Returns a reference to the [object](Pmw1Object) in which this executable's stack pointer is
    /// initially located.
    pub fn stack_object(&self) -> &Pmw1Object {
        self.object(self.stack_pointer().0 as usize).unwrap()
    }

    /// Returns a mutable reference to the [object](Pmw1Object) in which this executable's stack pointer is
    /// initially located.
    pub fn stack_object_mut(&mut self) -> &mut Pmw1Object {
        self.object_mut(self.stack_pointer().0 as usize).unwrap()
    }

    /// Sets the executable's initial stack pointer at `offset` in the memory space of the `obj_idx`th
    /// object. Remember, the objects are indexed starting from 1 rather than 0!
    ///
    /// ## Requirements:
    /// * `obj_idx` must refer to a valid object in the executable. Zero is never a valid index.
    /// * `offset` must be within the address space of the object (i.e. less than or equal to
    /// `self.objects(obj_idx as usize).virtual_size()`).
    pub fn set_stack_pointer(&mut self, obj_idx: u32, offset: u32) -> Result<()> {
        if let Some(obj) = self.object(obj_idx as usize) {
            if offset as usize <= obj.virtual_size() {
                self.stack_object = obj_idx;
                self.stack_pointer = offset;
                Ok(())
            } else {
                Err(Error::new(ErrorKind::InvalidInput, "Tried to set stack pointer outside the address space of its object!"))
            }
        } else {
            Err(Error::new(ErrorKind::InvalidInput, "Tried to set stack pointer in a non-existent object!"))
        }
    }

    /// Returns `true` if this executable is compressed, `false` otherwise.
    pub fn compressed(&self) -> bool {
        self.flag(0).unwrap()
    }

    /// Consumes this executable and returns an uncompressed version (or the same thing if
    /// it's already uncompressed).
    ///
    /// ## Details:
    /// The operation of "decompressing" an executable consists of modifying its `flags` and
    /// decompressing each of its objects in turn. Any failure to [decompress an
    /// object](Pmw1Object::decompress) bubbles up as a failure of this method.
    pub fn decompress(self) -> Result<Self> {
        if !self.compressed() {
            println!("Not compressed! Returning the same EXE...");
            return Ok(self);
        }

        Ok(Pmw1Exe {
            version_major:self.version_major,
            version_minor:self.version_minor,
            flags:self.flags & !0x1, // Not compressed
            entry_object:self.entry_object,
            entry_point:self.entry_point,
            stack_object:self.stack_object,
            stack_pointer:self.stack_pointer,

            objects:self.objects
                .into_iter()
                .enumerate()
                .map(|(i,x)| {
                    println!("Decompressing object {}...", i+1);
                    x.decompress()
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }

    /// Consumes this executable and returns an compressed version (or the same thing if
    /// it's already compressed).
    ///
    /// ## Details:
    /// The operation of "compressing" an executable consists of modifying its `flags` and
    /// compressing each of its objects in turn. Any failure to [compress an
    /// object](Pmw1Object::compress) bubbles up as a failure of this method.
    pub fn compress(self) -> Result<Self> {
        if self.compressed() {
            println!("Already compressed! Returning the same EXE...");
            return Ok(self);
        }

        Ok(Pmw1Exe {
            version_major:self.version_major,
            version_minor:self.version_minor,
            flags:self.flags | 0x1, // Compressed
            entry_object:self.entry_object,
            entry_point:self.entry_point,
            stack_object:self.stack_object,
            stack_pointer:self.stack_pointer,

            objects:self.objects
                .into_iter()
                .enumerate()
                .map(|(i,x)| {
                    println!("Compressing object {}...", i+1);
                    x.compress()
                })
                .collect::<Result<Vec<_>>>()?,
        })
    }

    /// Iterate over this executable's [objects](Pmw1Object).
    pub fn iter_objects(&self) -> std::slice::Iter<Pmw1Object> {
        self.objects.iter()
    }
    /// Iterate mutably over this executable's [objects](Pmw1Object).
    pub fn iter_objects_mut(&mut self) -> std::slice::IterMut<Pmw1Object> {
        self.objects.iter_mut()
    }

    /// Get a reference to the `obj_idx`th object in this executable. The indices start from 1, not
    /// 0! Returns [`None`] if an object with that index doesn't exist.
    pub fn object(&self, obj_idx: usize) -> Option<&Pmw1Object> {
        if obj_idx == 0 {
            println!("WARNING: PMW1 EXE objects are indexed starting from 1, not 0!");
            return None;
        }
        self.objects.get(obj_idx - 1)
    }
    /// Get a mutable reference to the `obj_idx`th object in this executable. The indices start from
    /// 1, not 0! Returns [`None`] if an object with that index doesn't exist.
    pub fn object_mut(&mut self, obj_idx: usize) -> Option<&mut Pmw1Object> {
        if obj_idx == 0 {
            println!("WARNING: PMW1 EXE objects are indexed starting from 1, not 0!");
            return None;
        }
        self.objects.get_mut(obj_idx - 1)
    }

    /// Collects all the data for this executable into a byte buffer, ready to be written back to a
    /// file. This is essentially the inverse of [`from_bytes`](Pmw1Exe::from_bytes), although it
    /// doesn't consume the executable.
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut objtab_buffer: Vec<u32> = Vec::with_capacity(0x400); // Modest size...
        let mut reloc_buffer: Vec<u8> = Vec::with_capacity(0x80000); // Decent size...
        let mut pages_buffer: Vec<u8> = Vec::with_capacity(0x100000); // Large size!

        for object in self.iter_objects() {
            objtab_buffer.extend(
                &object.to_tabentry(
                    // We'll be inserting this object's relocation blocks here in a moment:
                    reloc_buffer.len() as u32
                ));
            pages_buffer.extend(object.data_raw());

            for rblock in object.iter_reloc_blocks() {
                reloc_buffer.extend(rblock.as_bytes());
            }
        }

        let objtab_offset = 40; // This is the length of the PMW1 header. Object table should always come straight after it.
        let reloc_offset = objtab_offset + objtab_buffer.len()*4;
        let pages_offset = reloc_offset + reloc_buffer.len();

        let mut buffer: Vec<u8> = Vec::with_capacity(pages_offset + pages_buffer.len());
        buffer.extend(b"PMW1"); // Magic number
        buffer.extend(&[self.version_major,
                      self.version_minor]); // Two bytes
        // The rest of the header content is values that are wider than bytes.
        buffer.extend(self.flags.to_le_bytes().iter());
        buffer.extend(self.entry_object.to_le_bytes().iter());
        buffer.extend(self.entry_point.to_le_bytes().iter());
        buffer.extend(self.stack_object.to_le_bytes().iter());
        buffer.extend(self.stack_pointer.to_le_bytes().iter());
        buffer.extend((objtab_offset as u32).to_le_bytes().iter());
        buffer.extend((self.objects.len() as u32).to_le_bytes().iter());
        buffer.extend((reloc_offset as u32).to_le_bytes().iter());
        buffer.extend((pages_offset as u32).to_le_bytes().iter());

        // Now write in the object table itself...
        for int in objtab_buffer.iter() {
            buffer.extend(int.to_le_bytes().iter());
        }

        // And the relocation and page data.
        buffer.extend(reloc_buffer.iter());
        buffer.extend(pages_buffer.iter());

        buffer
    }
}
