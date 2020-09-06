pmw1-rs
=======

This is a Rust library for manipulating PMW1 executables. PMW1 is the compressible EXE format used by the [PMODE/W DOS Extender](http://www.sid6581.net/pmodew/).

This library allows analysing and (de-)compressing the individual components of a PMW1 EXE, mainly objects and relocation blocks.

# Example program

The program below takes the filename of a full PMW1 EXE file (including the DOS stub), decompresses and recompresses it. While doing so, it dumps the decompressed version to a file, dumps a bunch of data on the EXE's make-up to stdout, and also dumps the recompressed version to a file.

Note that both file dumps include the same DOS stub as the original EXE, which means that only one of them will actually run. This is because compression support is a compile-time switch in PMODE/W itself, and so a stub compiled for a compressed EXE will not be able to run an uncompressed one, or vice versa.

```rust
extern crate pmw1;

use std::env::args;
use std::io::prelude::*;
use std::fs::File;

use pmw1::exe::Pmw1Exe;

fn main() -> std::io::Result<()> {
    // Assume the filename of interest is the LAST argument on the command line.
    let exe_name: String = args().next_back().unwrap();

    // Load the whole EXE into memory...
    let binary = {
        println!("Opening {}...", exe_name);

        let mut file = File::open(&exe_name)?;
        let mut buffer: Vec<u8> = Vec::with_capacity(0x100000);
        file.read_to_end(&mut buffer)?;
        buffer.shrink_to_fit();
        buffer
    };

    println!("{} is {} bytes.", exe_name, binary.len());

    assert_eq!(binary[0..2],b"MZ"[..],
               "{} is not an MZ executable!", exe_name);
    assert!(binary.len() >= 0x1c,
            "{} doesn't appear to contain a complete MZ header!",exe_name);

    let mz_header = &binary[0x2..0x1c];
    let mz_header: Vec<u16> = (0..mz_header.len())
        .step_by(2)
        .map(|i| u16::from_le_bytes([mz_header[i], mz_header[i+1]]))
        .collect();

    // Print out some relevant info.
    println!("It begins with an MZ executable, of {} half-KiB blocks.",
             mz_header[1]);
    let total_block_size = mz_header[1] << 9; // Shift left to multiply by 512
    let actual_mz_size =
        if mz_header[0] == 0 {
            println!("Last block is fully used.");
            total_block_size
        } else {
            println!("{} bytes used in last block.", mz_header[0]);
            total_block_size - 512 + mz_header[0]
        } as usize;
    println!("Total MZ executable size is {} bytes.", actual_mz_size);

    assert!(binary.len() > actual_mz_size, "This appears to be a pure MZ executable!");

    // A slice containing just the PMW1 part.
    let pmw1_exe = Pmw1Exe::from_bytes(&binary[actual_mz_size..])?;

    // Is it all working??
    let pmw1_exe = pmw1_exe.decompress()?;
    {
        let mut outfile = File::create(&format!("{}.DECOMP",exe_name))?;
        // Write the DOS stub back out
        outfile.write_all(&binary[..actual_mz_size])?;
        // And the actual PMW1 exe!
        outfile.write_all(&pmw1_exe.as_bytes())?;
    }

    println!("{:#?}", pmw1_exe);

    // Try going back the other way...
    let pmw1_exe = pmw1_exe.compress()?;
    {
        let mut outfile = File::create(&format!("{}.RECOMP",exe_name))?;
        // Write the DOS stub back out
        outfile.write_all(&binary[..actual_mz_size])?;
        // And the actual PMW1 exe!
        outfile.write_all(&pmw1_exe.as_bytes())?;
    }

    Ok(())
}
```
