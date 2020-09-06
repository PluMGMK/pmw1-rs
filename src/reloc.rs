/*!
  Code for dealing with compressed and uncompressed relocation blocks in PMW1 EXE files.

  A relocation block is associated with a source object and contains up to thousands of entries, each specifying:
  * The relocation type
  * The source address in the source object's virtual memory space
  * The index of the target object (starting from 1, not 0)
  * The target address in the target object's virtual memory space
  */

use std::convert::TryInto; // To turn slices into arrays...

// It seems appropriate to craft I/O errors for this, instead of the overhead of maintaining my own
// error class...
use std::io::{Result,Error,ErrorKind};

use crate::codec::{encode,decode};
use crate::constants::*;

/// A simple struct representing a relocation block entry in a PMW1 executable.
///
/// All fields public since they are very simple to manipulate (although I don't
/// necessarily recommend trying it).
#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash,Default)]
pub struct Pmw1RelocEntry {
    /// Relocation type
    pub rtype:u8,
    /// Source address
    pub source:u32,
    /// Index of target object (starts from 1, not 0)
    pub target_obj:u8,
    /// Target address
    pub target:u32,
}

impl Pmw1RelocEntry {
    /// Create a new relocation block entry - can be used to (re-)build an entire PMW1 EXE from
    /// scratch.
    pub fn new(rtype:u8, target_obj:u8, source:u32, target:u32) -> Self {
        Pmw1RelocEntry {
            rtype:rtype,
            source:source,
            target_obj:target_obj,
            target:target,
        }
    }

    /// Takes exactly [`PMW1_RTABLE_ENTRY_SIZE`] bytes
    /// and interprets them as an uncompressed relocation entry.
    pub fn from_bytes(relocation_buf: &[u8; PMW1_RTABLE_ENTRY_SIZE]) -> Self {
        Pmw1RelocEntry::new(relocation_buf[0],
                            relocation_buf[5],
                            // Trying to read individual dwords here...
                            u32::from_le_bytes([relocation_buf[1],
                                               relocation_buf[2],
                                               relocation_buf[3],
                                               relocation_buf[4]]),
                            u32::from_le_bytes([relocation_buf[6],
                                               relocation_buf[7],
                                               relocation_buf[8],
                                               relocation_buf[9]]))
    }

    /// Takes exactly [`PMW1_RTABLE_ENTRY_SIZE`] bytes
    /// from an arbitrary position in a byte buffer and interprets them as an uncompressed
    /// relocation entry. Usually this buffer is a full relocation block, read in from a PMW1 EXE
    /// file.
    ///
    /// ## Requirements:
    /// * The length of the slice `relocation_buf` must be greater than or equal to `entry_offset +
    /// PMW1_RTABLE_ENTRY_SIZE`. Otherwise this fails with a [`std::io::Error`] of kind
    /// [`UnexpectedEof`](std::io::ErrorKind::UnexpectedEof).
    pub fn from_bytes_with_off(relocation_buf: &[u8], entry_offset:usize) -> Result<Self> {
        match relocation_buf.get(entry_offset..(entry_offset+PMW1_RTABLE_ENTRY_SIZE)) {
            Some(buf) => Ok(Pmw1RelocEntry::from_bytes(buf.try_into().unwrap())), // OK to unwrap here, since the slice is PMW1_RTABLE_ENTRY_SIZE in length
            None => Err(Error::new(ErrorKind::UnexpectedEof, "Incomplete relocation table entry")),
        }
    }

    /// Converts an uncompressed relocation block entry into a buffer of
    /// [`PMW1_RTABLE_ENTRY_SIZE`] bytes, so it can be
    /// compressed and/or written into a PMW1 EXE file. This is essentially the inverse of
    /// [`from_bytes`](Pmw1RelocEntry::from_bytes), although it doesn't consume the entry.
    pub fn as_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(PMW1_RTABLE_ENTRY_SIZE);
        bytes.push(self.rtype);
        bytes.extend(self.source.to_le_bytes().iter());
        bytes.push(self.target_obj);
        bytes.extend(self.target.to_le_bytes().iter());
        bytes
    }
}

#[derive(Debug,Clone,PartialEq,Eq,Hash)]
enum Pmw1RelocVec {
    Uncomp(Vec<Pmw1RelocEntry>),
    Comp(Vec<u8>),
}

impl Pmw1RelocVec {
    fn new(entries: Vec<Pmw1RelocEntry>) -> Self {
        Pmw1RelocVec::Uncomp(entries)
    }

    fn from_bytes(compressed:bool, table: &[u8]) -> Result<Self> {
        Ok(if compressed {
            // It's compressed, so just store it as-is for now.
            Pmw1RelocVec::Comp(table.to_vec())
        } else {
            // Uncompressed – process it into actual table entries!
            Pmw1RelocVec::Uncomp(
                (0..table.len())
                .step_by(PMW1_RTABLE_ENTRY_SIZE)
                .map(|off| {
                    Pmw1RelocEntry::from_bytes_with_off(table,off)
                }).collect::<Result<_>>()?)
        })
    }
}

/// A struct representing a full relocation block in a PMW1 EXE file, either compressed or
/// uncompressed.
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct Pmw1RelocBlock {
    //actual_size:u16,
    uncompressed_size:u16,
    table:Pmw1RelocVec,
}

impl Pmw1RelocBlock {
    /// Create a new relocation block, from an iterator of uncompressed entries. This can be used
    /// to (re-)build a PMW1 EXE from scratch.
    pub fn new(entries: &mut dyn Iterator<Item = Pmw1RelocEntry>) -> Self {
        let entries = entries.collect::<Vec<_>>();
        Pmw1RelocBlock {
            uncompressed_size:(entries.len() * PMW1_RTABLE_ENTRY_SIZE) as u16,
            table:Pmw1RelocVec::new(entries),
        }
    }

    /// Takes as many bytes as needed from an iterator, to create a valid relocation block, either
    /// compressed or uncompressed.
    ///
    /// ## Requirements:
    /// * The next four bytes from this iterator must be a valid relocation block header.
    /// * The iterator must be able to supply as many bytes beyond that as are specified in the
    /// block header itself (specifically, the [`u16`] encoded in the first two bytes).
    pub fn from_byte_iterator(relocation_buf_iter: &mut dyn Iterator<Item = &u8>) -> Result<Self> {
        // The metadata are made of words.
        let metadata: Vec<u8> = relocation_buf_iter.take(4).map(|&x| x).collect();
        let metadata: Vec<u16> = (0..metadata.len())
            .step_by(2)
            .map(|i| u16::from_le_bytes([metadata[i], metadata[i+1]]))
            .collect();

        let actual_size = metadata[0];
        let uncompressed_size = metadata[1];
        let table: Vec<u8> = relocation_buf_iter.take(actual_size as usize).map(|&x| x).collect();

        Ok(Pmw1RelocBlock {
            //actual_size:actual_size,
            uncompressed_size:uncompressed_size,
            table:Pmw1RelocVec::from_bytes(
                actual_size < uncompressed_size,
                &table)?,
        })
    }

    /// Returns the actual size in bytes of the full relocation table (i.e. the sum of all the
    /// entries).
    pub fn actual_size(&self) -> usize {
        match &self.table {
            Pmw1RelocVec::Comp(buf) => buf.len(),
            Pmw1RelocVec::Uncomp(table) => table.len() * PMW1_RTABLE_ENTRY_SIZE,
        }
    }

    /// Returns `true` if this block is compressed, `false` otherwise.
    pub fn compressed(&self) -> bool {
        match &self.table {
            Pmw1RelocVec::Comp(_) => true,
            Pmw1RelocVec::Uncomp(_) => false,
        }
    }

    /// Consumes this relocation block and returns an uncompressed version (or the same thing if
    /// it's already uncompressed).
    ///
    /// ## Requirements:
    /// * If this block is compressed, the data contained in it must be valid input for the PMW1
    /// decompression algorithm. Otherwise, this will fail with a [`std::io::Error`] of kind
    /// [`InvalidData`](std::io::ErrorKind::InvalidData).
    pub fn decompress(self) -> Result<Self> {
        match self.table {
            Pmw1RelocVec::Uncomp(_) => {
                println!("Not compressed! Returning the same relocation table...");
                Ok(self)
            },
            Pmw1RelocVec::Comp(table) => {
                let decoded_table = decode(&table, self.uncompressed_size as usize)?;
                if self.uncompressed_size as usize != decoded_table.len() {
                    return Err(Error::new(ErrorKind::InvalidData, "Decompressed relocation block size is not as advertised!"));
                }
                Ok(Pmw1RelocBlock {
                    // actual_size:self.uncompressed_size,
                    uncompressed_size:self.uncompressed_size,
                    table:Pmw1RelocVec::from_bytes(
                        false,
                        &decoded_table)?,
                })
            },
        }
    }

    /// Consumes this relocation block and returns a compressed version (or the same thing if
    /// it's already compressed).
    ///
    /// ## Requirements:
    /// * The data in this block must be at least two bytes long - in other words, there needs to
    /// be at least one entry. Otherwise, this will fail with a [`std::io::Error`] of kind
    /// [`InvalidData`](std::io::ErrorKind::InvalidData).
    pub fn compress(self) -> Result<Self> {
        match self.table {
            Pmw1RelocVec::Comp(_) => {
                println!("Already compressed! Returning the same relocation table...");
                Ok(self)
            },
            Pmw1RelocVec::Uncomp(ref table) => {
                let mut src_buffer: Vec<u8> = Vec::with_capacity(self.actual_size());
                for entry in table.iter() {
                    src_buffer.extend(entry.as_bytes());
                }

                Ok(Pmw1RelocBlock {
                    uncompressed_size:self.uncompressed_size,
                    table:Pmw1RelocVec::from_bytes(
                        true,
                        &encode(&src_buffer, NUM_PROBES)?)?,
                })
            },
        }
    }

    /// Converts a compressed or uncompressed relocation block into a buffer of bytes, so it can 
    /// be written into a PMW1 EXE file. This is essentially the inverse of
    /// [`from_byte_iterator`](Pmw1RelocBlock::from_byte_iterator), although it returns a
    /// `std::Vec` rather than an iterator.
    pub fn as_bytes(&self) -> Vec<u8> {
        let actual_size = self.actual_size();
        let mut buf: Vec<u8> = Vec::with_capacity(4 + actual_size);

        // Start with the size metadata.
        buf.extend((actual_size as u16).to_le_bytes().iter());
        buf.extend(self.uncompressed_size.to_le_bytes().iter());

        match &self.table {
            Pmw1RelocVec::Comp(table) => {
                buf.extend(table);
            },
            Pmw1RelocVec::Uncomp(table) => {
                for entry in table.iter() {
                    buf.extend(entry.as_bytes());
                }
            }
        }

        buf
    }

    /// Iterate over this block's [entries](Pmw1RelocEntry), if it is uncompressed.
    ///
    /// Returns [`None`] if this block is compressed. Decompress it before using this method.
    pub fn iter_reloc_entries(&self) -> Option<std::slice::Iter<Pmw1RelocEntry>> {
        match &self.table {
            Pmw1RelocVec::Comp(_) => None,
            Pmw1RelocVec::Uncomp(table) => Some(table.iter()),
        }
    }

    /// Iterate mutably over this block's [entries](Pmw1RelocEntry), if it is uncompressed.
    ///
    /// Returns [`None`] if this block is compressed. Decompress it before using this method.
    pub fn iter_reloc_entries_mut(&mut self) -> Option<std::slice::IterMut<Pmw1RelocEntry>> {
        match &mut self.table {
            Pmw1RelocVec::Comp(_) => None,
            Pmw1RelocVec::Uncomp(table) => Some(table.iter_mut()),
        }
    }
}
