// Decoding mov instructions in 8086. Yes. It took me 400 LoC to do this.
// Segment register related instructions are still missing

const PRINT_HEADER: bool = true; // print information required to successfully pipe the output and
                                 // assemble

macro_rules! read_byte {
    ($stream:ident, $index:ident) => {{
        assert!($stream.len() - $index >= 1, "Byte stream is empty!");
        $index += 1;
        $stream[$index - 1]
    }};
}

macro_rules! read_two_bytes {
    ($stream:ident, $index:ident) => {{
        assert!($stream.len() - $index >= 2,);
        let (b1, b2) = match &$stream[$index..] {
            &[first, second, ..] => (first, second),
            _ => panic!("Byte stream does not has 2 bytes to read from!"),
        };
        $index += 2;
        (b1, b2)
    }};
}

macro_rules! get_rm {
    ($opcode:ident) => {{
        $opcode & 0b00000111
    }};
}

macro_rules! get_mod {
    ($opcode:ident) => {{
        ($opcode & 0b11000000) >> 6
    }};
}

macro_rules! get_w {
    ($opcode:ident) => {{
        if $opcode & 0b00000001 == 1 {
            true
        } else {
            false
        }
    }};
}

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() != 2 {
        eprintln!("usage: {} <asm-filename>", args[0]);
        std::process::exit(-1);
    }

    // read input into a u8 vector
    let input: Vec<u8> = match std::fs::read(&args[1]) {
        Ok(bytes) => bytes,
        Err(e) => panic!("{}", e),
    };

    // current number of processed bytes in byte stream from the main binary
    let mut processed_count = 0;

    if PRINT_HEADER {
        println!("bits 16\n");
    }

    loop {
        // first byte when decoding each new instrucrion
        let opcode_byte = match &input[processed_count..] {
            &[first, ..] => {
                processed_count += 1;
                first
            }
            _ => break, // no more bytes
        };

        // Immediate to register
        if opcode_byte & 0b11110000 == 0b10110000 {
            // contains word
            let w = if opcode_byte & 0b00001000 == 0b00001000 {
                true
            } else {
                false
            };

            let reg = opcode_byte & 0b00000111;

            if w {
                let data = read_two_bytes!(input, processed_count);
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                println!("{}", format!("mov {}, {}", register_name(reg, w), immed16));
            } else {
                let immed8 = read_byte!(input, processed_count);
                println!("{}", format!("mov {}, {}", register_name(reg, w), immed8));
            }

            continue;
        }

        // register/memory to/from register
        if opcode_byte & 0b11111100 == 0b10001000 {
            // contains word
            let w = match opcode_byte & 0b00000001 {
                0b1 => true,
                0b0 => false,
                _ => unreachable!(),
            };

            // reg field is destination register
            let d = match opcode_byte & 0b00000010 {
                0b10 => true,
                0b00 => false,
                _ => unreachable!(),
            };

            let byte_2 = read_byte!(input, processed_count);

            // extract mod field from 2nd byte
            let mode = (byte_2 & 0b11000000) >> 6;

            // extract reg field from 2nd byte
            let reg: u8 = (byte_2 & 0b00111000) >> 3;

            // extract r/m field from 2nd byte
            let rm: u8 = byte_2 & 0b00000111;

            if mode == 0b11 {
                // register to register move

                // source register
                let src = if d { rm } else { reg };

                // destination register
                let dst = if d { reg } else { rm };

                println!(
                    "{}",
                    format!(
                        "mov {}, {}",
                        register_name(dst, w),
                        register_name(src, w).to_owned()
                    )
                );
            } else if mode == 0b00 {
                if rm == 0b110 {
                    // Direct Access
                    let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                    let d16 = ((d16_hi as u16) << 8) + d16_lo as u16;

                    let (dst, src) = if d {
                        // reg contains destination register. Memory to register move
                        (
                            register_name(reg, w).to_owned(),
                            format!("[{}]", d16), // Direct Access
                        )
                    } else {
                        // reg contains source register. Register to memory move
                        (
                            format!("[{}]", d16), // Direct Access
                            register_name(reg, w).to_owned(),
                        )
                    };
                    println!("mov {}, {}", dst, src);
                    continue;
                }

                let (dst, src) = if d {
                    // reg contains destination register. Memory to register move
                    (
                        register_name(reg, w).to_owned(),
                        format!("[{}]", address_register_part(rm)),
                    )
                } else {
                    // reg contains source register. Register to memory move
                    (
                        format!("[{}]", address_register_part(rm)),
                        register_name(reg, w).to_owned(),
                    )
                };

                println!("mov {}, {}", dst, src);
            } else if mode == 0b01 {
                // 8-bit displacement

                // displacement byte
                let d8 = read_byte!(input, processed_count);

                let (dst, src) = if d {
                    // reg contains destination register. Memory to register move
                    (
                        register_name(reg, w).to_owned(),
                        format!("[{} + {}]", address_register_part(rm), d8),
                    )
                } else {
                    // reg contains source register. Register to memory move
                    (
                        format!("[{} + {}]", address_register_part(rm), d8),
                        register_name(reg, w).to_owned(),
                    )
                };
                println!("mov {}, {}", dst, src);
            } else {
                // mode == 0b10
                // 16-bit displacement

                // displacement byte
                let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                let d16 = ((d16_hi as u16) << 8) + d16_lo as u16;

                let (dst, src) = if d {
                    // reg contains destination register. Memory to register move
                    (
                        register_name(reg, w).to_owned(),
                        format!("[{} + {}]", address_register_part(rm), d16),
                    )
                } else {
                    // reg contains source register. Register to memory move
                    (
                        format!("[{} + {}]", address_register_part(rm), d16),
                        register_name(reg, w).to_owned(),
                    )
                };
                println!("mov {}, {}", dst, src);
            }

            continue;
        }

        // Immediate to register/memory
        if opcode_byte & 0b11111110 == 0b11000110 {
            let w = get_w!(opcode_byte);
            let reg = "ax"; // other 7 registers are not used in this mode
            let byte_2 = read_byte!(input, processed_count);
            let mode = get_mod!(byte_2);
            let rm = get_rm!(byte_2);

            if mode == 0b00 {
                // No displacement
                if rm == 0b110 {
                    // Direct Access
                    let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                    let d16 = ((d16_hi as u16) << 8) + d16_lo as u16;
                    let dst = format!("[{}]", d16); // Direct Access

                    if w {
                        let data = read_two_bytes!(input, processed_count);
                        let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                        println!("mov {}, word {}", dst, immed16);
                    } else {
                        let immed8 = read_byte!(input, processed_count);
                        println!("mov {}, byte {}", dst, immed8);
                    }
                    continue;
                }

                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = address_register_part(rm);
                    println!("mov [{}], word {}", dst, immed16);
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = address_register_part(rm);
                    println!("mov [{}], byte {}", dst, immed8);
                }
            } else if mode == 0b01 {
                // 8-bit displacement
                let d8 = read_byte!(input, processed_count);
                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = format!("{} + {}", address_register_part(rm), d8);
                    println!("mov [{}], word {}", dst, immed16);
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = format!("{} + {}", address_register_part(rm), d8);
                    println!("mov [{}], byte {}", dst, immed8);
                }
            } else if mode == 0b10 {
                // 16-bit displacement
                let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                let d16 = ((d16_hi as u16) << 8) + d16_lo as u16;
                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = format!("{} + {}", address_register_part(rm), d16);
                    println!("mov [{}], word {}", dst, immed16);
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = format!("{} + {}", address_register_part(rm), d16);
                    println!("mov [{}], byte {}", dst, immed8);
                }
            } else {
                // mode == 0b11
                // Immediate to register (ax)

                if w {
                    // next two bytes contain data
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;

                    println!("mov {reg}, {}", immed16);
                } else {
                    let immed8 = read_byte!(input, processed_count);

                    println!("mov {reg}, {}", immed8);
                }
            }

            continue;
        }

        // Memory to accumulator move
        if opcode_byte & 0b11111110 == 0b10100000 {
            let (addr_lo, addr_hi) = read_two_bytes!(input, processed_count);
            let addr = ((addr_hi as u16) << 8) + addr_lo as u16;
            let w = get_w!(opcode_byte);

            if w {
                // move word from address to ax
                let dst = "ax";
                println!("mov {}, [{}]", dst, addr);
            } else {
                let dst = "al";
                // move byte from address to al
                println!("mov {}, [{}]", dst, addr);
            }

            continue;
        }

        // Accumulator to memory
        if opcode_byte & 0b11111110 == 0b10100010 {
            let (addr_lo, addr_hi) = read_two_bytes!(input, processed_count);
            let addr = ((addr_hi as u16) << 8) + addr_lo as u16;
            let w = get_w!(opcode_byte);

            if w {
                // move ax to memory address
                let src = "ax";
                println!("mov [{}], {}", addr, src);
            } else {
                // move al to memory address
                let src = "al";
                println!("mov [{}], {}", addr, src);
            }
        }
    }
}

// register part in memory address without the displacement
fn address_register_part(rm: u8) -> &'static str {
    match rm {
        0b000 => "bx + si",
        0b001 => "bx + di",
        0b010 => "bp + si",
        0b011 => "bp + di",
        0b100 => "si",
        0b101 => "di",
        0b110 => "bp",
        0b111 => "bx",
        _ => unreachable!(),
    }
}

// returns the register name based on the three bit register identifier 'reg' and one bit 'w' flag
fn register_name(reg: u8, w: bool) -> &'static str {
    match reg {
        0b000 if w => "ax",
        0b000 if !w => "al",
        0b001 if w => "cx",
        0b001 if !w => "cl",
        0b010 if w => "dx",
        0b010 if !w => "dl",
        0b011 if w => "bx",
        0b011 if !w => "bl",
        0b100 if w => "sp",
        0b100 if !w => "ah",
        0b101 if w => "bp",
        0b101 if !w => "ch",
        0b110 if w => "si",
        0b110 if !w => "dh",
        0b111 if w => "di",
        0b111 if !w => "bh",
        _ => unreachable!(),
    }
}
