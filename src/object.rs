/*!
  Code for dealing with compressed and uncompressed objects in PMW1 EXE files.

  Each object contains code and data, and some basic directions for mapping it into memory.
  It also has associated relocation blocks, to handle relocating data into the memory space of other objects.
  */

use std::convert::TryInto; // To turn slices into arrays...

// It seems appropriate to craft I/O errors for this, instead of the overhead of maintaining my own
// error class...
use std::io::{Result,Error,ErrorKind};

use crate::codec::{encode,decode};
use crate::reloc::Pmw1RelocBlock;
use crate::constants::*;

/// A struct representing an object in a PMW1 executable, and containing its associated relocation
/// blocks.
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct Pmw1Object {
    virtual_size:u32,
    //actual_size:u32,
    flags:u32,
    relocation_blocks:Vec<Pmw1RelocBlock>,
    uncompressed_size:u32,
    data:Vec<u8>,
}

impl Pmw1Object {
    /// Create a new object - can be used to (re-)build an entire PMW1 EXE from
    /// scratch.
    ///
    /// ## Details:
    /// This function allows you to specify:
    /// * The object's raw `data`, as a slice of bytes.
    /// * The relocation blocks, by passing a mutable iterator over [`Pmw1RelocBlock`]s.
    /// * The object's `virtual_size`, in bytes (i.e. how much memory is mapped at runtime for this
    /// object).
    /// * The object's `flags`, as a 32-bit-string. I don't know if any of these flags is used at all
    /// by PMODE/W.
    pub fn new(data: &[u8], reloc_blocks: &mut dyn Iterator<Item = Pmw1RelocBlock>, virtual_size:u32, flags:u32) -> Self {
        Pmw1Object {
            virtual_size: virtual_size,
            flags: flags,
            relocation_blocks: reloc_blocks.collect(),
            // This is for building an object from scratch, so data should come uncompressed.
            uncompressed_size: data.len() as u32,
            data:data.to_vec(),
        }
    }

    /// Turn an entry from a PMW1 EXE file's object table into an actual object, including its data
    /// and relocation blocks.
    ///
    /// ## Details:
    /// This function facilitates building an object from data scattered at various locations in
    /// an EXE file. As such, you need to pass three different things:
    /// * The `table_entry` itself, as a slice of bytes as they are read from the EXE file's object
    /// table.
    /// * A buffer containing *all* the bytes in the EXE that are designated as relocation data.
    /// The data stored in the table entry indicates where exactly to look in the buffer for this
    /// object's relocation blocks.
    /// * An iterator over the bytes in the data-pages block of the EXE, with its current position
    /// at the start of this object's data.
    ///
    /// ## Requirements:
    /// * The length of `table_entry` must be exactly four times [`PMW1_OBJTABLE_ENTRY_LENGTH`],
    /// otherwise you will get a [`std::io::Error`] of kind
    /// [`InvalidData`](ErrorKind::InvalidData).
    /// * `relocation_buf` and `data_iter` must be able to supply as much data as is specified in
    /// `table_entry` - see the requirements on [`from_tabentry`](Pmw1Object::from_tabentry) for
    /// more details.
    pub fn from_tabentry_byteslice(table_entry: &[u8], relocation_buf: &[u8], data_iter: &mut dyn Iterator<Item = &u8>) -> Result<Self> {
        // Object table entries are made up of dwords.
        if (table_entry.len() % 4) != 0 {
            return Err(Error::new(ErrorKind::InvalidData, "Table entry size not a multiple of 4 (i.e. 32 bits)"));
        }
        let table_entry: Vec<u32> = (0..table_entry.len())
            .step_by(4)
            .map(|i| u32::from_le_bytes([table_entry[i],
                                        table_entry[i+1],
                                        table_entry[i+2],
                                        table_entry[i+3]]))
            .collect();
        Pmw1Object::from_tabentry_slice(&table_entry, relocation_buf, data_iter)
    }

    /// Turn an entry from a PMW1 EXE file's object table into an actual object, including its data
    /// and relocation blocks. This function assumes you have already converted the entry into
    /// 32-bit integers.
    ///
    /// ## Details:
    /// This function facilitates building an object from data scattered at various locations in
    /// an EXE file. As such, you need to pass three different things:
    /// * The `table_entry` itself, as a slice of 32-bit integers as they are encoded in the EXE
    /// file's object table.
    /// * A buffer containing *all* the bytes in the EXE that are designated as relocation data.
    /// The data stored in the table entry indicates where exactly to look in the buffer for this
    /// object's relocation blocks.
    /// * An iterator over the bytes in the data-pages block of the EXE, with its current position
    /// at the start of this object's data.
    ///
    /// ## Requirements:
    /// * The length of `table_entry` must be exactly [`PMW1_OBJTABLE_ENTRY_LENGTH`],
    /// otherwise you will get a [`std::io::Error`] of kind
    /// [`InvalidData`](ErrorKind::InvalidData).
    /// * `relocation_buf` and `data_iter` must be able to supply as much data as is specified in
    /// `table_entry` - see the requirements on [`from_tabentry`](Pmw1Object::from_tabentry) for
    /// more details.
    pub fn from_tabentry_slice(table_entry: &[u32], relocation_buf: &[u8], data_iter: &mut dyn Iterator<Item = &u8>) -> Result<Self> {
        Pmw1Object::from_tabentry(
                match table_entry.try_into() {
                    Ok(arr) => arr,
                    Err(_) => return Err(Error::new(ErrorKind::InvalidData, "Wrong object table entry length")),
                },
                relocation_buf,
                data_iter)
    }

    /// Turn an entry from a PMW1 EXE file's object table into an actual object, including its data
    /// and relocation blocks. This function assumes you have already converted the entry into
    /// 32-bit integers, and that you're in a position to pass them as a fixed-size array.
    ///
    /// ## Details:
    /// This function facilitates building an object from data scattered at various locations in
    /// an EXE file. As such, you need to pass three different things:
    /// * The `table_entry` itself, as an array of [`PMW1_OBJTABLE_ENTRY_LENGTH`] 32-bit integers
    /// as they are encoded in the EXE file's object table.
    /// * A buffer containing *all* the bytes in the EXE that are designated as relocation data.
    /// The data stored in the table entry indicates where exactly to look in the buffer for this
    /// object's relocation blocks.
    /// * An iterator over the bytes in the data-pages block of the EXE, with its current position
    /// at the start of this object's data.
    ///
    /// ## Requirements:
    /// * The `relocation_buf` must be at least `table_entry[3]` bytes long, and contain as much
    /// data beyond that as is needed to construct `table_entry[4]` [`Pmw1RelocBlock`]s.
    /// * `data_iter` must be able to supply at least `table_entry[1]` bytes.
    pub fn from_tabentry(table_entry: &[u32; PMW1_OBJTABLE_ENTRY_LENGTH], relocation_buf: &[u8], data_iter: &mut dyn Iterator<Item = &u8>) -> Result<Self> {
        let mut relocation_buf_iter = match relocation_buf.get((table_entry[3] as usize)..) {
            Some(slice) => slice.iter(),
            None => return Err(Error::new(ErrorKind::UnexpectedEof, "Object claims relocation data are outside the designated region")),
        };

        Ok(Pmw1Object {
            virtual_size:table_entry[0],
            //actual_size:table_entry[1],
            flags:table_entry[2],
            relocation_blocks:
                (0..table_entry[4]).map(|_| {
                    Pmw1RelocBlock::from_byte_iterator(relocation_buf_iter.by_ref())
                }).collect::<Result<_>>()?,
            uncompressed_size:table_entry[5],
            data:data_iter.take(table_entry[1] as usize).map(|&x| x).collect(),
        })
    }

    /// Creates a PMW1 EXE file object table entry (i.e. [`PMW1_OBJTABLE_ENTRY_LENGTH`] 32-bit
    /// integers) to represent this object.
    ///
    /// ## Requirements:
    /// * When using this function to re-construct a PMW1 EXE file, you must know where exactly
    /// this object's relocation blocks will be inserted into the file's relocation data section.
    /// This position needs to be passed as `relocation_pos`.
    pub fn to_tabentry(&self, relocation_pos: u32) -> [u32; PMW1_OBJTABLE_ENTRY_LENGTH] {
        [self.virtual_size,
        self.actual_size() as u32,
        self.flags,
        // This object doesn't know what the relocation buffer of its parent looks like, so this
        // parameter has to be passed to the function:
        relocation_pos, 
        self.relocation_blocks.len() as u32,
        self.uncompressed_size]
    }

    /// Returns this object's `n`th flag, as a [`bool`].
    ///
    /// ## Requirements:
    /// * `n` must be less than 32, since there are only 32 flag bits in total.
    pub fn flag(&self, n:u8) -> Result<bool> {
        if (n >> 5) != 0 {
            Err(Error::new(ErrorKind::InvalidInput, "Trying to read object flag beyond 31"))
        } else {
            Ok((self.flags & (1 << n)) != 0)
        }
    }

    /// Sets this object's `n`th flag according to `val` (1 if `true`, 0 if `false`).
    ///
    /// ## Requirements:
    /// * `n` must be less than 32, since there are only 32 flag bits in total.
    pub fn set_flag(&mut self, n:u8, val:bool) -> Result<()> {
        if (n >> 5) != 0 {
            Err(Error::new(ErrorKind::InvalidInput, "Trying to write object flag beyond 31"))
        } else {
            if val {
                self.flags |= 1 << n;
            } else {
                self.flags &= !(1 << n);
            }
            Ok(())
        }
    }

    /// Consumes this object and returns an uncompressed version (or the same thing if
    /// it's already uncompressed).
    ///
    /// ## Requirements:
    /// * If this object is compressed, the data contained in it must be valid input for the PMW1
    /// decompression algorithm.
    /// * `self.uncompressed_size` must match the actual size produced by the decompression
    /// algorithm. This is a private field, but it can be updated by 
    /// [`update_data_raw`](Pmw1Object::update_data_raw).
    /// * The same must apply to each of this object's relocation blocks.
    ///
    /// If any of these is violated, this will fail with a [`std::io::Error`] of kind
    /// [`InvalidData`](ErrorKind::InvalidData).
    pub fn decompress(self) -> Result<Self> {
        if !self.compressed() {
            println!("Not compressed! Returning the same object...");
            return Ok(self);
        }

        let newobj = Pmw1Object {
            virtual_size:self.virtual_size,
            //actual_size:self.uncompressed_size,
            flags:self.flags,
            relocation_blocks:
                self.relocation_blocks
                .into_iter()
                .map(|x| x.decompress())
                .collect::<Result<Vec<_>>>()?,
            uncompressed_size:self.uncompressed_size,
            data:decode(&self.data, self.uncompressed_size as usize)?,
        };

        if newobj.actual_size() != newobj.uncompressed_size() {
            Err(Error::new(ErrorKind::InvalidData, "Decompressed object size is not as advertised!"))
        } else {
            Ok(newobj)
        }
    }

    /// Consumes this object and returns a compressed version (or the same thing if
    /// it's already compressed).
    ///
    /// ## Requirements:
    /// * The object's data must be at least two bytes long. Otherwise, this will fail
    /// with a [`std::io::Error`] of kind [`InvalidData`](ErrorKind::InvalidData).
    /// * Each of this object's relocation blocks must similarly be compressible.
    pub fn compress(self) -> Result<Self> {
        if self.compressed() {
            println!("Already compressed! Returning the same object...");
            return Ok(self);
        }

        Ok(Pmw1Object {
            virtual_size:self.virtual_size,
            flags:self.flags,
            relocation_blocks:
                self.relocation_blocks
                .into_iter()
                .map(|x| x.compress())
                .collect::<Result<Vec<_>>>()?,
            uncompressed_size:self.uncompressed_size,
            data:encode(&self.data, NUM_PROBES)?,
        })
    }

    /// Returns the current physical size of this object's data, in bytes.
    pub fn actual_size(&self) -> usize {
        self.data.len()
    }

    /// Returns the virtual size in bytes of this object, i.e. how much memory is mapped for it at
    /// runtime.
    pub fn virtual_size(&self) -> usize {
        self.virtual_size as usize
    }

    /// Sets the virtual size in bytes of the object, i.e. how much memory is mapped for it at
    /// runtime.
    ///
    /// I don't know if there are legitimate use-cases for this, but I might as well include it.
    /// *Caveat programmer*.
    pub fn set_virtual_size(&mut self, new_size: u32) {
        self.virtual_size = new_size as u32;
    }

    /// Returns the size in bytes that this object currently believes its data will occupy when
    /// uncompressed.
    ///
    /// I say "believes" because careless use of [`update_data_raw`](Pmw1Object::update_data_raw)
    /// can cause this to go out of sync.
    pub fn uncompressed_size(&self) -> usize {
        self.uncompressed_size as usize
    }

    /// Returns `true` if this object is compressed, `false` otherwise.
    pub fn compressed(&self) -> bool {
        self.actual_size() < self.uncompressed_size()
    }

    /// Returns a slice of bytes containing the data currently stored in this object, regardless of
    /// whether it's compressed or not.
    pub fn data_raw(&self) -> &[u8] {
        &self.data
    }

    /// Returns a [`Vec`] of bytes containing this object's actual code/data, decompressing it if
    /// necessary.
    pub fn data(&self) -> Result<Vec<u8>> {
        let raw_data = self.data_raw();
        if self.compressed() {
            decode(raw_data, self.uncompressed_size as usize)
        } else {
            Ok(raw_data.to_vec())
        }
    }

    /// Applies a closure `f` to the data currently stored in this object, regardless of whether
    /// it's compressed or not.
    ///
    /// ## WARNING:
    /// This function is not `unsafe`, in that it can't cause undefined behaviour in Rust itself,
    /// but it can mess up the state of your object if you're not careful! If you know what you're
    /// doing, calling this function on a compressed object with a carefully-crafted closure may be
    /// faster than [`update_data`](Pmw1Object::update_data), which would decompress, apply the
    /// closure and then recompress the data. However, it is *your* responsibility to make sure
    /// that you know exactly what the uncompressed size of the updated data will be! If
    /// `new_uncompressed_size` is mis-specified here, then you can no longer trust the
    /// [`compressed`](Pmw1Object::compressed) method, or any other method that relies on it, and
    /// your EXE file will likely malfunction when you run it!
    ///
    /// *You have been warned!*
    pub fn update_data_raw<F>(&mut self, f: F, new_uncompressed_size: u32) 
    where F: FnOnce(&[u8]) -> Vec<u8> { 
        self.data = f(self.data_raw());
        self.uncompressed_size = new_uncompressed_size;
    }

    /// Applies a closure `f` to the actual code/data of this object, decompressing and
    /// recompressing it if necessary. The `uncompressed_size` field is updated automatically.
    pub fn update_data<F>(&mut self, f: F) -> Result<()>
        // If I use &str as the error type, the borrow checker gets its knickers in a twist.
        // If I use String, the &str silently gets converted as it bubbles up, and it compiles
        // grand. Go fig...
    where F: FnOnce(&[u8]) -> Vec<u8> { 
        let compressed = self.compressed(); // Store this now since we can't rely on this function when we update self.uncompressed_size!
        let new_data = f(&self.data()?);

        self.uncompressed_size = new_data.len() as u32;
        self.data = if compressed {
            encode(&new_data, NUM_PROBES)?
        } else {
            new_data
        };

        Ok(())
    }

    /// Iterate over this object's [relocation blocks](Pmw1RelocBlock).
    pub fn iter_reloc_blocks(&self) -> std::slice::Iter<Pmw1RelocBlock> {
        self.relocation_blocks.iter()
    }

    /// Iterate mutably over this object's [relocation blocks](Pmw1RelocBlock).
    pub fn iter_reloc_blocks_mut(&mut self) -> std::slice::IterMut<Pmw1RelocBlock> {
        self.relocation_blocks.iter_mut()
    }
}
