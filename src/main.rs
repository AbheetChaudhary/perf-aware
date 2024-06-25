// Decoding mov instructions in 8086. Yes. It took me 400 LoC to do this.
// Segment register related instructions are still missing

use std::collections::HashMap;

const PRINT_HEADER: bool = true; // print information required to successfully pipe the output and
                                 // assemble. Simply print 'bits 16' at the top

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
    ($byte:ident) => {{
        $byte & 0b00000111
    }};
}

macro_rules! get_mod {
    ($byte:ident) => {{
        ($byte & 0b11000000) >> 6
    }};
}

/*
macro_rules! get_reg {
    ($byte:ident) => {{
        ($byte & 0b00111000) >> 3
    }}
}
*/

macro_rules! get_w {
    ($opcode:ident) => {{
        if $opcode & 0b00000001 == 1 {
            true
        } else {
            false
        }
    }};
}

macro_rules! add_inst_to_buffer {
    ($inst_addr:ident, $position:ident, $format_string:literal, $($var:expr),*) => {
        $inst_addr.push(InstAddr::new($position, format!($format_string, $($var),*)));
    }
}

/*
macro_rules! get_d {
    ($opcode:ident) => {{
        if $opcode & 0b00000010 == 0b10 {
            true
        } else {
            false
        }
    }};
}
*/

struct InstAddr {
    addr: usize,  // position of the byte from the beginning of the binary
    inst: String, // instruction string
}

impl InstAddr {
    fn new(addr: usize, inst: String) -> Self {
        InstAddr { addr, inst }
    }
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

    let mut inst_addr: Vec<InstAddr> = Vec::new();
    let mut lable_map: HashMap<usize, String> = HashMap::new();

    loop {
        let processed_count_prev = processed_count;
        // first byte when decoding each new instrucrion
        let opcode_byte = match &input[processed_count..] {
            &[first, ..] => {
                processed_count += 1;
                first
            }
            _ => break, // no more bytes
        };

        // MOV - immediate to register
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
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "mov {}, {}",
                    register_name(reg, w),
                    immed16
                );
            } else {
                let immed8 = read_byte!(input, processed_count);
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "mov {}, {}",
                    register_name(reg, w),
                    immed8
                );
            }

            continue;
        }

        // MOV - register/memory to/from register
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

                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "mov {}, {}",
                    register_name(dst, w),
                    register_name(src, w).to_owned()
                );
            } else if mode == 0b00 {
                if rm == 0b110 {
                    // Direct Access
                    let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                    let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;

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
                    add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, {}", dst, src);
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

                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, {}", dst, src);
            } else if mode == 0b01 {
                // 8-bit displacement

                // displacement byte
                let d8 = read_byte!(input, processed_count) as i8 as i16; // sign extend to 16-bits

                let (dst, src) = if d {
                    // reg contains destination register. Memory to register move
                    (
                        register_name(reg, w).to_owned(),
                        if d8 > 0 {
                            format!("[{} + {}]", address_register_part(rm), d8)
                        } else if d8 < 0 {
                            // multiplying with -1 wont overflow because before being a word, it
                            // was originally a negative signed byte
                            format!("[{} - {}]", address_register_part(rm), -1 * d8)
                        } else {
                            format!("[{}]", address_register_part(rm))
                        },
                    )
                } else {
                    // reg contains source register. Register to memory move
                    (
                        if d8 > 0 {
                            format!("[{} + {}]", address_register_part(rm), d8)
                        } else if d8 < 0 {
                            // multiplying with -1 wont overflow because before being a word, it
                            // was originally a negative signed byte
                            format!("[{} - {}]", address_register_part(rm), -1 * d8)
                        } else {
                            format!("[{}]", address_register_part(rm))
                        },
                        register_name(reg, w).to_owned(),
                    )
                };
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, {}", dst, src);
            } else {
                // mode == 0b10
                // 16-bit displacement

                // displacement byte
                let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;

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
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, {}", dst, src);
            }

            continue;
        }

        // MOV - immediate to register/memory
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
                    let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;
                    let dst = format!("[{}]", d16); // Direct Access

                    if w {
                        let data = read_two_bytes!(input, processed_count);
                        let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                        add_inst_to_buffer!(
                            inst_addr,
                            processed_count_prev,
                            "mov {}, word {}",
                            dst,
                            immed16
                        );
                    } else {
                        let immed8 = read_byte!(input, processed_count);
                        add_inst_to_buffer!(
                            inst_addr,
                            processed_count_prev,
                            "mov {}, byte {}",
                            dst,
                            immed8
                        );
                    }
                    continue;
                }

                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = address_register_part(rm);
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], word {}",
                        dst,
                        immed16
                    );
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = address_register_part(rm);
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], byte {}",
                        dst,
                        immed8
                    );
                }
            } else if mode == 0b01 {
                // 8-bit displacement
                let d8 = read_byte!(input, processed_count) as i8 as i16;
                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = if d8 > 0 {
                        format!("[{} + {}]", address_register_part(rm), d8)
                    } else if d8 < 0 {
                        // multiplying with -1 wont overflow because before being a word, it
                        // was originally a negative signed byte
                        format!("[{} - {}]", address_register_part(rm), -1 * d8)
                    } else {
                        format!("[{}]", address_register_part(rm))
                    };
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], word {}",
                        dst,
                        immed16
                    );
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = if d8 > 0 {
                        format!("[{} + {}]", address_register_part(rm), d8)
                    } else if d8 < 0 {
                        // multiplying with -1 wont overflow because before being a word, it
                        // was originally a negative signed byte
                        format!("[{} - {}]", address_register_part(rm), -1 * d8)
                    } else {
                        format!("[{}]", address_register_part(rm))
                    };
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], byte {}",
                        dst,
                        immed8
                    );
                }
            } else if mode == 0b10 {
                // 16-bit displacement
                let (d16_lo, d16_hi) = read_two_bytes!(input, processed_count);
                let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;
                if w {
                    // next two bytes contain immed16
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    let dst = format!("{} + {}", address_register_part(rm), d16);
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], word {}",
                        dst,
                        immed16
                    );
                } else {
                    // next one byte contains immed8
                    let immed8 = read_byte!(input, processed_count);
                    let dst = format!("{} + {}", address_register_part(rm), d16);
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "mov [{}], byte {}",
                        dst,
                        immed8
                    );
                }
            } else {
                // mode == 0b11
                // Immediate to register (ax)

                if w {
                    // next two bytes contain data
                    let data = read_two_bytes!(input, processed_count);
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;

                    add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {reg}, {}", immed16);
                } else {
                    let immed8 = read_byte!(input, processed_count);

                    add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {reg}, {}", immed8);
                }
            }

            continue;
        }

        // MOV - Memory to accumulator move
        if opcode_byte & 0b11111110 == 0b10100000 {
            let (addr_lo, addr_hi) = read_two_bytes!(input, processed_count);
            let addr = ((addr_hi as u16) << 8) + addr_lo as u16;
            let w = get_w!(opcode_byte);

            if w {
                // move word from address to ax
                let dst = "ax";
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, [{}]", dst, addr);
            } else {
                let dst = "al";
                // move byte from address to al
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov {}, [{}]", dst, addr);
            }

            continue;
        }

        // MOV - accumulator to memory
        if opcode_byte & 0b11111110 == 0b10100010 {
            let (addr_lo, addr_hi) = read_two_bytes!(input, processed_count);
            let addr = ((addr_hi as u16) << 8) + addr_lo as u16;
            let w = get_w!(opcode_byte);

            if w {
                // move ax to memory address
                let src = "ax";
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov [{}], {}", addr, src);
            } else {
                // move al to memory address
                let src = "al";
                add_inst_to_buffer!(inst_addr, processed_count_prev, "mov [{}], {}", addr, src);
            }

            continue;
        }

        // ADD - reg/memory with register to either - 000000dw as opcode
        // SUB - reg/memory and register to either - 001010dw as opcode
        // CMP - reg/memory and register - 001110dw as opcode
        if opcode_byte & 0b11000100 == 0b00000000 {
            let inst = match (opcode_byte & 0b00111000) >> 3 {
                /* ADD */ 0b000 => "add",
                /* SUB */ 0b101 => "sub",
                /* CMP */ 0b111 => "cmp",
                _ => unreachable!(),
            };
            mod_reg_rm_disp(
                inst,
                opcode_byte,
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut inst_addr,
            );
            continue;
        }

        // ADD/SUB/CMP - immediate to register/memory - 100000sw as opcode
        if opcode_byte & 0b11111100 == 0b10000000 {
            let w = get_w!(opcode_byte);
            let byte_2 = read_byte!(input, processed_count);
            let mode = get_mod!(byte_2);
            let rm = get_rm!(byte_2);
            let reg = register_name(rm, w); // rm is used to encode register
            let inst = match (byte_2 & 0b00111000) >> 3 {
                /* ADD */ 0b000 => "add",
                /* SUB */ 0b101 => "sub",
                /* CMP */ 0b111 => "cmp",
                _ => unreachable!(),
            };
            mod_rm_disp_data(
                inst,
                opcode_byte,
                mode,
                rm,
                reg,
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut inst_addr,
            );
            continue;
        }

        // ADD/SUB/CMP - immediate to accumulator
        if opcode_byte & 0b11000110 == 0b00000100 {
            let inst = match (opcode_byte & 0b00111000) >> 3 {
                /* ADD */ 0b000 => "add",
                /* SUB */ 0b101 => "sub",
                /* CMP */ 0b111 => "cmp",
                _ => unreachable!(),
            };

            let w = get_w!(opcode_byte);
            if w {
                let data = read_two_bytes!(input, processed_count);
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                add_inst_to_buffer!(inst_addr, processed_count_prev, "{inst} ax, {}", immed16);
            } else {
                let immed8 = read_byte!(input, processed_count);
                add_inst_to_buffer!(inst_addr, processed_count_prev, "{inst} al, {}", immed8);
            }

            continue;
        }

        // different kinds of conditional jump and some loop instructions
        match opcode_byte {
            // conditional jump instructions
            /*   JE/JZ */
            0b01110100 => manage_jump_inst(
                "je",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JL/JNGE */
            0b01111100 => manage_jump_inst(
                "jl",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JLE/JNG */
            0b01111110 => manage_jump_inst(
                "jle",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JB/JNAE */
            0b01110010 => manage_jump_inst(
                "jb",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JBE/JNA */
            0b01110110 => manage_jump_inst(
                "jbe",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*  JP/JPE */
            0b01111010 => manage_jump_inst(
                "jp",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*      JO */
            0b01110000 => manage_jump_inst(
                "jo",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*      JS */
            0b01111000 => manage_jump_inst(
                "js",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNE/JNZ */
            0b01110101 => manage_jump_inst(
                "jnz",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNL/JGE */
            0b01111101 => manage_jump_inst(
                "jnl",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNLE/JG */
            0b01111111 => manage_jump_inst(
                "jg",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNB/JAE */
            0b01110011 => manage_jump_inst(
                "jnb",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNBE/JA */
            0b01110111 => manage_jump_inst(
                "ja",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* JNP/JPO */
            0b01111011 => manage_jump_inst(
                "jnp",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*     JNO */
            0b01110001 => manage_jump_inst(
                "jno",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*     JNS */
            0b01111001 => manage_jump_inst(
                "jns",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*    JCXZ */
            0b11100011 => manage_jump_inst(
                "jcxz",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),

            // loop instructions
            /*          LOOP */
            0b11100010 => manage_jump_inst(
                "loop",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /*   LOOPZ/LOOPE */
            0b11100001 => manage_jump_inst(
                "loopz",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            /* LOOPNZ/LOOPNE */
            0b11100000 => manage_jump_inst(
                "loopnz",
                &input,
                &mut processed_count,
                processed_count_prev,
                &mut lable_map,
                &mut inst_addr,
            ),
            _ => unreachable!(),
        }
    }

    // loop is done, now print each istruction and required lables
    for e in &inst_addr {
        if let Some(lable) = lable_map.remove(&e.addr) {
            println!("\n{}:", lable);
            println!("{}", e.inst);
        } else {
            println!("{}", e.inst);
        }
    }
}

fn manage_jump_inst(
    inst_name: &str,
    input: &Vec<u8>,
    processed_count: &mut usize,
    processed_count_prev: usize,
    lable_map: &mut HashMap<usize, String>,
    inst_addr: &mut Vec<InstAddr>,
) {
    let ipinc8 = match &input[*processed_count..] {
        &[first, ..] => first,
        _ => panic!("Byte stream is empty. Not a single byte to read!"),
    } as i8 as isize;
    *processed_count += 1;

    let addr = (*processed_count as isize + ipinc8) as usize; // byte address in the binary
    let lable = if lable_map.contains_key(&addr) {
        lable_map.get(&addr).unwrap().as_str()
    } else {
        let lable_count = lable_map.len();
        lable_map.insert(addr, format!("lable{:0>3}", lable_count));
        lable_map.get(&addr).unwrap().as_str()
    };
    add_inst_to_buffer!(inst_addr, processed_count_prev, "{} {}", inst_name, lable);
}

// helper function when only d, w, mod r/m, disp-lo, disp-hi, data are needed
fn mod_rm_disp_data(
    inst_name: &str,
    opcode_byte: u8,
    mode: u8,
    rm: u8,
    reg: &str,
    input: &Vec<u8>,
    processed_count: &mut usize,
    processed_count_prev: usize,
    inst_addr: &mut Vec<InstAddr>,
) {
    let w = match opcode_byte & 0b00000001 {
        1 => true,
        _ => false,
    };

    let s = match opcode_byte & 0b00000010 {
        0b10 => true,
        0b00 => false,
        _ => unreachable!(),
    };

    if mode == 0b00 {
        // No displacement
        if rm == 0b110 {
            // Direct Access
            let (d16_lo, d16_hi) = match &input[*processed_count..] {
                &[first, second, ..] => (first, second),
                _ => panic!("Byte stream does not has 2 bytes to read from!"),
            };
            *processed_count += 2;

            let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;
            let dst = format!("[{}]", d16); // Direct Access

            if w {
                if s {
                    let immed8 = match &input[*processed_count..] {
                        &[first, ..] => first,
                        _ => panic!("Byte stream is empty. Not a single byte to read!"),
                    } as i8 as i16;
                    *processed_count += 1;
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "{inst_name} {}, word {}",
                        dst,
                        immed8
                    );
                } else {
                    let data = match &input[*processed_count..] {
                        &[first, second, ..] => (first, second),
                        _ => panic!("Byte stream does not has 2 bytes to read from!"),
                    };
                    *processed_count += 2;
                    let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                    add_inst_to_buffer!(
                        inst_addr,
                        processed_count_prev,
                        "{inst_name} {}, word {}",
                        dst,
                        immed16
                    );
                }
            } else {
                let immed8 = match &input[*processed_count..] {
                    &[byte, ..] => byte,
                    _ => panic!("Byte stream is empty. Not a single byte to read!"),
                };
                *processed_count += 1;

                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} {}, byte {}",
                    dst,
                    immed8
                );
            }
            return;
        }

        if w {
            // next two bytes contain immed16
            if s {
                let immed8 = match &input[*processed_count..] {
                    &[first, ..] => first,
                    _ => panic!("Byte stream is empty. Not a single byte to read!"),
                } as i8 as i16;
                *processed_count += 1;
                let dst = address_register_part(rm);
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed8
                );
            } else {
                let data = match &input[*processed_count..] {
                    &[first, second, ..] => (first, second),
                    _ => panic!("Byte stream does not has 2 bytes to read from!"),
                };
                *processed_count += 2;
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                let dst = address_register_part(rm);
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed16
                );
            }
        } else {
            // next one byte contains immed8
            let immed8 = match &input[*processed_count..] {
                &[byte, ..] => byte,
                _ => panic!("Byte stream is empty. Not a single byte to read!"),
            };
            *processed_count += 1;

            let dst = address_register_part(rm);
            add_inst_to_buffer!(
                inst_addr,
                processed_count_prev,
                "{inst_name} [{}], byte {}",
                dst,
                immed8
            );
        }
    } else if mode == 0b01 {
        // 8-bit displacement
        let d8 = match &input[*processed_count..] {
            &[byte, ..] => byte,
            _ => panic!("Byte stream is empty. Not a single byte to read!"),
        } as i8 as i16;
        *processed_count += 1;

        if w {
            let dst = if d8 > 0 {
                format!("[{} + {}]", address_register_part(rm), d8)
            } else if d8 < 0 {
                // multiplying with -1 wont overflow because before being a word, it
                // was originally a negative signed byte
                format!("[{} - {}]", address_register_part(rm), -1 * d8)
            } else {
                format!("[{}]", address_register_part(rm))
            };

            if s {
                let immed8 = match &input[*processed_count..] {
                    &[first, ..] => first,
                    _ => panic!("Byte stream is empty. Not a single byte to read!"),
                } as i8 as i16;
                *processed_count += 1;
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed8
                );
            } else {
                // next two bytes contain immed16
                let data = match &input[*processed_count..] {
                    &[first, second, ..] => (first, second),
                    _ => panic!("Byte stream does not has 2 bytes to read from!"),
                };
                *processed_count += 2;
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed16
                );
            }
        } else {
            // next one byte contains immed8
            let immed8 = match &input[*processed_count..] {
                &[byte, ..] => byte,
                _ => panic!("Byte stream is empty. Not a single byte to read!"),
            };
            *processed_count += 1;
            let dst = if d8 > 0 {
                format!("[{} + {}]", address_register_part(rm), d8)
            } else if d8 < 0 {
                // multiplying with -1 wont overflow because before being a word, it
                // was originally a negative signed byte
                format!("[{} - {}]", address_register_part(rm), -1 * d8)
            } else {
                format!("[{}]", address_register_part(rm))
            };
            add_inst_to_buffer!(
                inst_addr,
                processed_count_prev,
                "{inst_name} [{}], byte {}",
                dst,
                immed8
            );
        }
    } else if mode == 0b10 {
        // 16-bit displacement
        let (d16_lo, d16_hi) = match &input[*processed_count..] {
            &[first, second, ..] => (first, second),
            _ => panic!("Byte stream does not has 2 bytes to read from!"),
        };
        *processed_count += 2;
        let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;
        if w {
            if s {
                let immed8 = match &input[*processed_count..] {
                    &[first, ..] => first,
                    _ => panic!("Byte stream is empty. Not a single byte to read!"),
                } as i8 as i16;
                *processed_count += 1;
                let dst = format!("{} + {}", address_register_part(rm), d16);
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed8
                );
            } else {
                // next two bytes contain immed16
                let data = match &input[*processed_count..] {
                    &[first, second, ..] => (first, second),
                    _ => panic!("Byte stream does not has 2 bytes to read from!"),
                };
                *processed_count += 2;
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                let dst = format!("{} + {}", address_register_part(rm), d16);
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} [{}], word {}",
                    dst,
                    immed16
                );
            }
        } else {
            // next one byte contains immed8
            let immed8 = match &input[*processed_count..] {
                &[byte, ..] => byte,
                _ => panic!("Byte stream is empty. Not a single byte to read!"),
            };
            *processed_count += 1;
            let dst = format!("{} + {}", address_register_part(rm), d16);
            add_inst_to_buffer!(
                inst_addr,
                processed_count_prev,
                "{inst_name} [{}], byte {}",
                dst,
                immed8
            );
        }
    } else {
        // mode == 0b11
        // Immediate to register

        if w {
            if s {
                let immed8 = match &input[*processed_count..] {
                    &[first, ..] => first,
                    _ => panic!("Byte stream is empty. Not a single byte to read!"),
                } as i8 as i16;
                *processed_count += 1;
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} {reg}, {}",
                    immed8
                );
            } else {
                // next two bytes contain immed16
                let data = match &input[*processed_count..] {
                    &[first, second, ..] => (first, second),
                    _ => panic!("Byte stream does not has 2 bytes to read from!"),
                };
                *processed_count += 2;
                let immed16 = ((data.1 as u16) << 8) + data.0 as u16;
                add_inst_to_buffer!(
                    inst_addr,
                    processed_count_prev,
                    "{inst_name} {reg}, {}",
                    immed16
                );
            }
        } else {
            let immed8 = match &input[*processed_count..] {
                &[byte, ..] => byte,
                _ => panic!("Byte stream is empty. Not a single byte to read!"),
            };
            *processed_count += 1;

            add_inst_to_buffer!(
                inst_addr,
                processed_count_prev,
                "{inst_name} {reg}, {}",
                immed8
            );
        }
    }
}

// helper function when only d, w, mod, reg, r/m, disp-lo, disp-hi are needed
fn mod_reg_rm_disp(
    inst_name: &str,
    opcode_byte: u8,
    input: &Vec<u8>,
    processed_count: &mut usize,
    processed_count_prev: usize,
    inst_addr: &mut Vec<InstAddr>,
) {
    let w = match opcode_byte & 0b00000001 {
        1 => true,
        _ => false,
    };
    let d = match opcode_byte & 0b00000010 {
        0b10 => true,
        0b00 => false,
        _ => unreachable!(),
    };

    let byte_2 = match &input[*processed_count..] {
        &[byte, ..] => byte,
        _ => panic!("Byte stream is empty. Not a single byte to read!"),
    };
    *processed_count += 1;

    let mode = (byte_2 & 0b11000000) >> 6;
    let reg = (byte_2 & 0b00111000) >> 3;
    let rm = byte_2 & 0b00000111;
    if mode == 0b11 {
        // register to register operation

        // source register
        let src = if d { rm } else { reg };

        // destination register
        let dst = if d { reg } else { rm };

        add_inst_to_buffer!(
            inst_addr,
            processed_count_prev,
            "{inst_name} {}, {}",
            register_name(dst, w),
            register_name(src, w).to_owned()
        );
    } else if mode == 0b00 {
        if rm == 0b110 {
            // Direct Access
            let (d16_lo, d16_hi) = match &input[*processed_count..] {
                &[first, second, ..] => (first, second),
                _ => panic!("Byte stream does not has 2 bytes to read from!"),
            };
            *processed_count += 2;
            let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;

            let (dst, src) = if d {
                // reg contains destination register. Memory to register operation
                (
                    register_name(reg, w).to_owned(),
                    format!("[{}]", d16), // Direct Access
                )
            } else {
                // reg contains source register. Register to memory operation
                (
                    format!("[{}]", d16), // Direct Access
                    register_name(reg, w).to_owned(),
                )
            };
            add_inst_to_buffer!(
                inst_addr,
                processed_count_prev,
                "{inst_name} {}, {}",
                dst,
                src
            );

            return;
        }

        let (dst, src) = if d {
            // reg contains destination register. Memory to register operation
            (
                register_name(reg, w).to_owned(),
                format!("[{}]", address_register_part(rm)),
            )
        } else {
            // reg contains source register. Register to memory operation
            (
                format!("[{}]", address_register_part(rm)),
                register_name(reg, w).to_owned(),
            )
        };

        add_inst_to_buffer!(
            inst_addr,
            processed_count_prev,
            "{inst_name} {}, {}",
            dst,
            src
        );
    } else if mode == 0b01 {
        // 8-bit displacement

        // displacement byte
        let d8 = match &input[*processed_count..] {
            &[byte, ..] => byte,
            _ => panic!("Byte stream is empty. Not a single byte to read!"),
        } as i8 as i16; // sign extend to 16-bits
        *processed_count += 1;

        let (dst, src) = if d {
            // reg contains destination register. Memory to register operation
            (
                register_name(reg, w).to_owned(),
                if d8 > 0 {
                    format!("[{} + {}]", address_register_part(rm), d8)
                } else if d8 < 0 {
                    // multiplying with -1 wont overflow because before being a word, it
                    // was originally a negative signed byte
                    format!("[{} - {}]", address_register_part(rm), -1 * d8)
                } else {
                    format!("[{}]", address_register_part(rm))
                },
            )
        } else {
            // reg contains source register. Register to memory operation
            (
                if d8 > 0 {
                    format!("[{} + {}]", address_register_part(rm), d8)
                } else if d8 < 0 {
                    // multiplying with -1 wont overflow because before being a word, it
                    // was originally a negative signed byte
                    format!("[{} - {}]", address_register_part(rm), -1 * d8)
                } else {
                    format!("[{}]", address_register_part(rm))
                },
                register_name(reg, w).to_owned(),
            )
        };
        add_inst_to_buffer!(
            inst_addr,
            processed_count_prev,
            "{inst_name} {}, {}",
            dst,
            src
        );
    } else {
        // mode == 0b10
        // 16-bit displacement

        // displacement byte
        let (d16_lo, d16_hi) = match &input[*processed_count..] {
            &[first, second, ..] => (first, second),
            _ => panic!("Byte stream does not has 2 bytes to read from!"),
        };
        *processed_count += 2;
        let d16 = (((d16_hi as u16) << 8) + d16_lo as u16) as i16;

        let (dst, src) = if d {
            // reg contains destination register. Memory to register operation
            (
                register_name(reg, w).to_owned(),
                format!("[{} + {}]", address_register_part(rm), d16),
            )
        } else {
            // reg contains source register. Register to memory operation
            (
                format!("[{} + {}]", address_register_part(rm), d16),
                register_name(reg, w).to_owned(),
            )
        };
        add_inst_to_buffer!(
            inst_addr,
            processed_count_prev,
            "{inst_name} {}, {}",
            dst,
            src
        );
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
