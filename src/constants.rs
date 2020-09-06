/*!
  Useful constants for manipulating PMW1 EXE files - mainly sizes of header entries.
  */

//pub const NUM_PROBES: usize = 2; // Default value of "ct" in the original PMWLITE.C
pub const NUM_PROBES: usize = 4; // Maximum value

pub const PMW1_RTABLE_ENTRY_SIZE:usize = 0xA;
pub const PMW1_OBJTABLE_ENTRY_LENGTH:usize = 6;
pub const PMW1_OBJTABLE_ENTRY_SIZE:usize = PMW1_OBJTABLE_ENTRY_LENGTH*4; // Each item is 32 bits = 4 bytes
