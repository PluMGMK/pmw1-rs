/*!
  A Rust library for manipulating PMW1 executables. PMW1 is the compressible EXE format used by the [PMODE/W DOS Extender](http://www.sid6581.net/pmodew/).

  This crate is pretty rough and ready, but currently you can see an example program on [GitHub](https://github.com/PluMGMK/pmw1-rs).
  */

#![feature(asm)]
#![feature(cell_update)]

#![doc(html_root_url = "https://docs.rs/pmw1/0.1.0")]

pub mod constants;
mod codec; // Internal
pub mod reloc;
pub mod object;
pub mod exe;
