/*!
  Implementation of PMW1 EXE-compression codec - partly idiomatic Rust, but with a lot of inline assembly!
  For this reason, it works only on x86 (but at least this includes x86_64).

  Note that most of the above-mentioned inline assembly comes directly from the freely-available 
  [PMODE/W source distribution](http://www.sid6581.net/pmodew/) - this may be a licensing concern!
  The original authors state: "Due to the fact that PMODE/W is no longer supported it is now free for use
  in commercial and non-commercial applications, provided said applications are not themselves DOS extenders.
  To put it bluntly, don't go ripping off our DOS extender to make your own."

  So one should be OK to use this crate for manipulating EXE files, but not for actually making a DOS extender.
  As intriguing a notion as it is to write a DOS extender in Rust, I think we should all be fine with this restriction!
  */

use std::collections::HashMap;
use std::arch::asm;

// For moving stuff around between various closures in the "compress" function. I'm definitely not
// a fan of how this was done with global variables in the original C code!
use std::cell::{Cell,RefCell};

// It seems appropriate to craft I/O errors for this, instead of the overhead of maintaining my own
// error class...
use std::io::{Result,Error,ErrorKind};

/// Takes a slice of bytes and runs the PMW1 decompression algorithm on them, returning a
/// `std::Vec` of bytes with the uncompressed data.
///
/// ## Details:
/// * The meat of this function is inline assembly, copied almost directly from the original
/// [PMODE/W source distribution](http://www.sid6581.net/pmodew/).
/// * Bounds checks have been added to avoid marking this function as `unsafe`
/// * This includes both the original 32-bit code and a 64-bit translation by yours truly, to avoid
/// needing 32-bit support on modern systems.
///
/// ## Requirements:
/// * The slice `coded_buf` must contain valid compressed data. Otherwise you will get either
/// garbage or (more likely) a `std::io::Error` of type `InvalidData`.
/// * The size of the uncompressed data must be less than or (ideally) equal to `uncompressed_size`
/// bytes. Otherwise you will get a `std::io::Error` of type `WriteZero`.
pub fn decode(coded_buf: &[u8], expected_size: usize) -> Result<Vec<u8>> {
    let mut destination_buf = Vec::with_capacity(expected_size);

    let source_ptr = coded_buf.as_ptr();
    let mut dest_ptr: *mut u8 = destination_buf.as_mut_ptr();

    // Constants for bounds checking
    let source_bufhead = source_ptr as usize;
    let source_bufend = source_bufhead + coded_buf.len();
    let dest_bufhead = dest_ptr as usize;
    let dest_bufend = dest_bufhead + destination_buf.capacity();

    // The following inline Assembly is almost directly copied from the freely-available DECODE.ASM
    // file, part of the PMODE/W source distribution obtained from http://www.sid6581.net/pmodew/,
    // with the following changes:
    // 1. All comments stripped out, since Rust doesn't recognize the semicolon.
    // 2. All @@ labels given unique names (as mandated at least by UASM) and the '@@' changed to
    //    'l' since Rust doesn't like that symbol either.
    // 3. The "decode_read" function has been removed, since we know in advance that our source
    //    buffer is filled with exactly as much data as needed to perform the decompression. Both
    //    calls to it, and relevant esi manipulations, have been removed, *BUT* the initial call has
    //    been replaced with a "xor ecx,ecx", which was a required side-effect!
    // 4. There's a little wrapper on the top to make sure it plays well with Rust. In particular,
    //    Rust doesn't allow us to specify ebp as a scratch register (or any other type), so a
    //    manual push and pop are used instead. This is a blessing in disguise, as it prevents
    //    compilation in 64-bit mode (which would expect to see "push rbp" instead). Otherwise, it
    //    would be possible to compile this in 64-bit mode, but it would segfault immediately from
    //    trying to use 32-bit pointers! UPDATE: Actually now I've protected it with a cfg
    //    directive, and written a new 64-bit version below. :)
    // 5. Added a bunch of bounds checking to avoid having to mark this function as unsafe. This
    //    probably makes the code a lot less efficient than the original was (lots of extra cmps
    //    involving the stack) but I doubt anyone will be running this on a 386... Note that the
    //    two cmps in "decode_getbit" use slightly different addresses because they're inside a
    //    subroutine and so the stack pointer will be four bytes lower.
    #[cfg(target_pointer_width = "32")]
    #[allow(named_asm_labels)]
    unsafe{asm!("
        push ebp
        call decode
        pop ebp
        jmp _endinline

decode:
        push eax
        push ebx
        push ecx
        push edx

        xor ecx,ecx

        cmp esi, [esp+0Ch]
        jb _oob
        cmp esi, [esp+8h]
        jge _oob
        cmp edi, [esp+4h]
        jb _oob
        cmp edi, [esp]
        jge _enddecode

        movs byte ptr es:[edi],byte ptr es:[esi]
        xor dl,dl

        jmp short decode_decode

decode_extended:
        call decode_getbit
        jnc short decode_length

        call decode_getbit
        adc cl,1
        shl cl,1

l01l:
        call decode_getbit
        rcl bh,1
        loop l01l

decode_length:
        mov dh,2
        mov cl,4

l02l:
        inc dh
        call decode_getbit
        jc short decode_movestringdh

        loop l02l

        call decode_getbit
        jnc short decode_length3bit

        cmp esi, [esp+0Ch]
        jb _oob
        cmp esi, [esp+8h]
        jge _oob

        lods byte ptr es:[esi]
        mov cl,al
        add ecx,15
        jmp short decode_movestring

decode_length3bit:
        xor dh,dh
        mov cl,3

l03l:
        call decode_getbit
        rcl dh,1
        loop l03l

        add dh,7

decode_movestringdh:
        mov cl,dh
        jmp short decode_movestring

decode_movestring2:
        mov cl,2

decode_movestring:
        neg ebx
        dec ebx

l04l:
        add edi,ebx
        cmp edi, [esp+4h]
        jb _oob
        cmp edi, [esp]
        jge _enddecode
        mov al,es:[edi]
        sub edi,ebx

        cmp edi, [esp+4h]
        jb _oob
        cmp edi, [esp]
        jge _enddecode
        stos byte ptr es:[edi]
        loop l04l

decode_decode:


l00:
        call decode_getbit
        jc short code

        cmp esi, [esp+0Ch]
        jb _oob
        cmp esi, [esp+8h]
        jge _oob
        cmp edi, [esp+4h]
        jb _oob
        cmp edi, [esp]
        jge _enddecode

        movs byte ptr es:[edi],byte ptr es:[esi]
        jmp decode_decode

code:
        xor ebx,ebx

        cmp esi, [esp+0Ch]
        jb _oob
        cmp esi, [esp+8h]
        jge _oob

        lods byte ptr es:[esi]
        mov bl,al

        call decode_getbit
        jc short decode_extended

        call decode_getbit
        jc short decode_code11

        dec ebx
        jns decode_movestring2

        jmp _enddecode

_oob:
        xor edi,edi
_enddecode:

        pop edx
        pop ecx
        pop ebx
        pop eax
        ret

decode_code11:
        mov cl,3

l05l:
        call decode_getbit
        rcl bh,1
        loop l05l

        jmp short decode_movestring2


decode_getbit:
        dec dl
        jns short l01

        cmp esi, [esp+10h]
        jb _getbit_oob
        cmp esi, [esp+0Ch]
        jge _getbit_oob

        lods dword ptr es:[esi]
        mov ebp,eax
        mov dl,31

l01:
        shl ebp,1

        ret

_getbit_oob:
        xor edi,edi
        ret

_endinline:
        ",
        inout("esi") source_ptr => _,
        inout("edi") dest_ptr,
        in("eax") source_bufhead,
        in("ebx") source_bufend,
        in("ecx") dest_bufhead,
        in("edx") dest_bufend
            );
    }

    // Here's a 64-bit version, taking advantage of extra registers so the stack is no longer
    // involved in the bounds checks!
    #[cfg(target_pointer_width = "64")]
    #[allow(named_asm_labels)]
    unsafe{asm!("
        push rbp
        push rbx
        call decode
        pop rbx
        pop rbp
        jmp _endinline

decode:

        xor rcx,rcx

        cmp rsi,r8
        jb _oob
        cmp rsi,r9
        jge _oob
        cmp rdi,r10
        jb _oob
        cmp rdi,r11
        jge _enddecode

        movs byte ptr es:[rdi],byte ptr es:[rsi]
        xor dl,dl

        jmp short decode_decode

decode_extended:
        call decode_getbit
        jnc short decode_length

        call decode_getbit
        adc cl,1
        shl cl,1

l01l:
        call decode_getbit
        rcl bh,1
        loop l01l

decode_length:
        mov dh,2
        mov cl,4

l02l:
        inc dh
        call decode_getbit
        jc short decode_movestringdh

        loop l02l

        call decode_getbit
        jnc short decode_length3bit

        cmp rsi,r8
        jb _oob
        cmp rsi,r9
        jge _oob

        lods byte ptr es:[rsi]
        mov cl,al
        add ecx,15
        jmp short decode_movestring

decode_length3bit:
        xor dh,dh
        mov cl,3

l03l:
        call decode_getbit
        rcl dh,1
        loop l03l

        add dh,7

decode_movestringdh:
        mov cl,dh
        jmp short decode_movestring

decode_movestring2:
        mov cl,2

decode_movestring:
        neg rbx
        dec rbx

l04l:
        add rdi,rbx
        cmp rdi,r10
        jb _oob
        cmp rdi,r11
        jge _enddecode
        mov al,es:[rdi]
        sub rdi,rbx

        cmp rdi,r10
        jb _oob
        cmp rdi,r11
        jge _enddecode
        stos byte ptr es:[rdi]
        loop l04l

decode_decode:


l00:
        call decode_getbit
        jc short code

        cmp rsi,r8
        jb _oob
        cmp rsi,r9
        jge _oob
        cmp rdi,r10
        jb _oob
        cmp rdi,r11
        jge _enddecode

        movs byte ptr es:[rdi],byte ptr es:[rsi]
        jmp decode_decode

code:
        xor rbx,rbx

        cmp rsi,r8
        jb _oob
        cmp rsi,r9
        jge _oob

        lods byte ptr es:[rsi]
        mov bl,al

        call decode_getbit
        jc short decode_extended

        call decode_getbit
        jc short decode_code11

        dec rbx
        jns decode_movestring2

        jmp _enddecode

_oob:
        xor rdi,rdi
_enddecode:

        ret

decode_code11:
        mov cl,3

l05l:
        call decode_getbit
        rcl bh,1
        loop l05l

        jmp short decode_movestring2


decode_getbit:
        dec dl
        jns short l01

        cmp rsi,r8
        jb _getbit_oob
        cmp rsi,r9
        jge _getbit_oob

        lods dword ptr es:[rsi]
        mov ebp,eax
        mov dl,31

l01:
        shl ebp,1

        ret

_getbit_oob:
        xor rdi,rdi
        ret

_endinline:
        ",
        inout("rsi") source_ptr => _,
        inout("rdi") dest_ptr,
        in("r8") source_bufhead,
        in("r9") source_bufend,
        in("r10") dest_bufhead,
        in("r11") dest_bufend,
        out("rax") _,
        out("rcx") _,
        out("rdx") _,
            );
    }

    // Figure out how far edi has moved.
    if dest_ptr.is_null() {
        // This means the "xor edi,edi" (or "xor rdi,rdi") above has been executed!
        return Err(Error::new(ErrorKind::InvalidData,"Decompression algorithm went outside buffer bounds – probably bad input"));
    }
    let decoded_size = (dest_ptr as usize) - dest_bufhead;
    if decoded_size > destination_buf.capacity() {
        return Err(Error::new(ErrorKind::WriteZero,"Decompression buffer overflow"));
    }

    unsafe{
        // What could possibly go wrong?
        destination_buf.set_len(decoded_size);
    }
    destination_buf.shrink_to_fit();

    Ok(destination_buf)
}

/// Takes a slice of bytes and runs the PMW1 compression algorithm on them, returning a
/// `std::Vec` of bytes with the compressed data.
///
/// ## Details:
/// * The algorithm searches for recurrences of two-byte strings, then goes back through the buffer
/// up to `num_probes` times to find the longest string match it can (up to 270 bytes) beginning
/// with the same two bytes.
/// * The default `num_probes` value in the original PMWLITE.EXE was 2, and the maximum was 4. This
/// crate's struct methods use `constants::NUM_PROBES`, currently set to 4.
/// * String matches more than 4 kB earlier in the buffer are ignored.
///
/// ## Requirements:
/// * The slice `source_buf` must be at least two bytes long. Otherwise you will get
/// a `std::io::Error` of type `InvalidData`.
pub fn encode(source_buf: &[u8], probes: usize) -> Result<Vec<u8>> {
    // Translated into idiomatic Rust from the freely-available PMWLITE/ENCODE.C file,
    // part of the PMODE/W source distribution obtained from http://www.sid6581.net/pmodew/, taking
    // advantage of native Rust features like the HashMap.
    if source_buf.len() < 2 {
        return Err(Error::new(ErrorKind::InvalidData, "Data too small for compression!"));
    }

    let mut hash: HashMap<u16,Vec<i32>> = HashMap::new();
    let destination_buf = RefCell::new(Vec::with_capacity(source_buf.len())); // By definition, it will be shorter than this, so it's reasonable to allocate this much starting off.
    let l_pos = Cell::new(0usize);

    let hash_key_curpos = || {
        u16::from_le_bytes([source_buf[l_pos.get()],
                            match source_buf.get(l_pos.get()+1) {
                                Some(&byte) => byte,
                                None => 0,
                            }])
    };

    // OK since we've already made sure that source_buf is more than 2 bytes long.
    hash.insert(hash_key_curpos(), vec![0]);

    destination_buf.borrow_mut().push(source_buf[l_pos.get()]);
    l_pos.update(|x| x + 1);

    let l_size = Cell::new(source_buf.len() - 1);

    let buf_bit_buf = Cell::new(0i32);
    let buf_bit_count = Cell::new(0usize);

    let buf_byte_buf: RefCell<Vec<u8>> = RefCell::new(Vec::with_capacity(0x100)); // This is just for individual chunks...

    let flush_bit_buf = || {
        let mut dest = match destination_buf.try_borrow_mut() {
            Ok(vec) => vec,
            Err(_) => return Err(Error::new(ErrorKind::WouldBlock, "Error compressing: couldn't borrow destination buffer mutably!")),
        };

        dest.extend(buf_bit_buf.get().to_le_bytes().iter());
        Ok(())
    };

    let flush_byte_buf = || {
        let mut src = match buf_byte_buf.try_borrow_mut() {
            Ok(vec) => vec,
            Err(_) => return Err(Error::new(ErrorKind::WouldBlock, "Error compressing: couldn't borrow byte buffer mutably!")),
        };
        let mut dest = match destination_buf.try_borrow_mut() {
            Ok(vec) => vec,
            Err(_) => return Err(Error::new(ErrorKind::WouldBlock, "Error compressing: couldn't borrow destination buffer mutably!")),
        };

        dest.append(&mut src);
        Ok(())
    };

    let buf_put_bit = |bit: bool| -> Result<()> {
        buf_bit_buf.update(|x| x << 1);
        if bit {
            buf_bit_buf.update(|x| x | 1);
        }

        buf_bit_count.update(|x| x + 1);
        if buf_bit_count.get() == 1 {
            flush_byte_buf()?;
        } else if buf_bit_count.get() == 32 {
            flush_bit_buf()?;
            buf_bit_buf.set(0);
            buf_bit_count.set(0);
        }

        Ok(())
    };

    let buf_put_byte = |byte: u8| {
        let mut buf = match buf_byte_buf.try_borrow_mut() {
            Ok(vec) => vec,
            Err(_) => return Err(Error::new(ErrorKind::WouldBlock, "Error compressing: couldn't borrow byte buffer mutably!")),
        };

        buf.push(byte);
        Ok(())
    };

    let buf_put_bits = |b: i32, c: usize| -> Result<()> {
        let i = buf_bit_count.get();
        buf_bit_count.update(|x| x + c);

        if buf_bit_count.get() == c {
            buf_bit_buf.set(b);
            flush_byte_buf()?;
        } else if buf_bit_count.get() <= 32 {
            buf_bit_buf.update(|x| (x << c) | b);
            if buf_bit_count.get() == 32 {
                flush_bit_buf()?;
                buf_bit_buf.set(0);
                buf_bit_count.set(0);
            }
        } else {
            buf_bit_buf.set((buf_bit_buf.get() << (32 - i)) | (b >> (buf_bit_count.get() - 32)));
            flush_bit_buf()?;
            flush_byte_buf()?;
            buf_bit_count.update(|x| x - 32);
            buf_bit_buf.set(b & ((1 << buf_bit_count.get()) - 1));
        }

        Ok(())
    };

    while l_size.get() != 0 {
        // Changed PutCode from a function into an inline code block, since this is the only place
        // it was actually called from.
        let code_len = {
            if l_size.get() == 1 {
                buf_put_bit(false)?;
                buf_put_byte(source_buf[l_pos.get()])?;
                1
            } else {
                let mut len = 1usize;
                let mut off = 0i32; // This doesn't actually get initialized in the original C. Go fig...

                match hash.get(&hash_key_curpos()) {
                    Some(vec) => for (i2,&i0) in vec.iter().rev().enumerate() {
                        if i2 >= probes {
                            break;
                        }
                        let signed_ptr = source_buf.as_ptr() as isize;
                        let c = signed_ptr + (i0 as isize);
                        let i0 = (l_pos.get() as i32)-1 - i0;
                        let mut i1;
                        // StringMatch macro
                        unsafe{
                            asm!("
                            xor eax,eax
                            mov edx,ecx
                            repe cmpsb
                            setne al
                            add ecx,eax
                            sub edx,ecx
                            ",
                            // Use the "rXX" registers to make sure they work on 64-bit. Seems to
                            // still work on 32-bit...
                            inout("rdi") c => _,
                            inout("rsi") source_buf.as_ptr().add(l_pos.get()) => _,
                            inout("rcx") (if l_size.get() < 270 {l_size.get()} else {270}) => _,
                            out("rax") _,
                            out("rdx") i1);
                        }

                        if ((i1 == 2) && (i0 >= 0x800)) || (i0 >= 0x1000) {
                            // Don't end up with an offset more than 12 bits long!
                            // (Or 11 bits where the length is 2).
                            //
                            // NOTE: The original C code contained only the first check (11 bits in the
                            // length=2 case), because offsets *implicitly* couldn't be any longer than
                            // 12 bits due to the 4-kB buffer size. Here in Rust we're using
                            // arbitrary-sized buffers, which meant I was silently losing the MSBs on
                            // longer offsets until I brought in the second check.
                            //
                            // This had me scratching my head for WEEKS - I thought I had an off-by-one,
                            // but I actually had an off-by-4096, or off-by-8192, etc., depending on the
                            // situation!
                            continue;
                        }

                        if i1 > len {
                            off = i0;
                            len = i1;
                        }
                    },
                    None => {},
                }

                if len < 2 {
                    buf_put_bit(false)?;
                    buf_put_byte(source_buf[l_pos.get()])?;
                } else if len == 2 {
                    buf_put_bit(true)?;
                    
                    if off < 255 {
                        buf_put_byte(1 + (off as u8))?;
                        buf_put_bits(0, 2)?;
                    } else {
                        // In this case, the offset is still always < 0x800 (see above)
                        buf_put_byte((off & 0xff) as u8)?;
                        buf_put_bits(8 | ((off >> 8) & 7), 5)?;
                    }
                } else {
                    buf_put_bit(true)?;
                    buf_put_byte((off & 0xff) as u8)?;

                    if off < 0x100 {
                        buf_put_bits(2, 2)?;
                    } else if off < 0x400 {
                        buf_put_bits(0x18 | ((off >> 8) & 3), 5)?;
                    } else {
                        // In this case, the offset is still always < 0x1000 - in the original C code, this
                        // was the case due to the buffer size, but here I had to add an explicit check -
                        // see above!
                        buf_put_bits(0x70 | ((off >> 8) & 15), 7)?;
                    }

                    if len < 7 {
                        buf_put_bits(1, len - 2)?;
                    } else if len < 15 {
                        buf_put_bits(((len-7) & 7) as i32, 8)?;
                    } else {
                        buf_put_bits(1, 5)?;
                        // Maximum length is 270, so (len - 15) always fits in a u8.
                        buf_put_byte((len - 15) as u8)?;
                    }
                }

                len
            }
        };
        l_size.update(|x| x - code_len);

        // Bunch of stuff here to deal with the hash overflowing. We don't need to worry about
        // that since it's all abstracted away by Rust's std::collections API...
        
        for _ in 0..code_len {
            match hash.get_mut(&hash_key_curpos()) {
                Some(vec) => {vec.push(l_pos.get() as i32);},
                None => {hash.insert(hash_key_curpos(), vec![l_pos.get() as i32]);},
            }
            l_pos.update(|x| x + 1);
        }

        // Stuff here to make sure we don't overflow the buffers. Again, don't need to worry about
        // that since the in buffer has been passed to us with the exact length needed, and the out
        // buffer can be automatically grown if needs be by Rust's std::vec API.
    }

    buf_put_bit(true)?;
    buf_put_byte(0)?;
    buf_put_bits(0,2)?;

    // Flush out the last bits and bytes.
    if buf_bit_count.get() > 0 {
        buf_bit_buf.update(|x| x << (32 - buf_bit_count.get()));
        flush_bit_buf()?;
    }
    flush_byte_buf()?;

    // Finished borrowing this thing...
    let mut destination_buf = destination_buf.into_inner();
    destination_buf.shrink_to_fit();
    Ok(destination_buf)
}
