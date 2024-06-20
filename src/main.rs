// decoding move from register to register

use std::io::{BufReader, Read};

const PRINT_HEADER: bool = true; // print information required to successfully pipe the output and
                                 // assemble

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() != 2 {
        eprintln!("usage: {} <asm-filename>", args[0]);
        std::process::exit(-1);
    }

    let f = match std::fs::File::open(&args[1]) {
        Ok(file) => file,
        Err(e) => panic!("{}", e),
    };

    let mut reader = BufReader::new(f);

    let mut mov_bytes: [u8; 2] = [0, 0];

    if PRINT_HEADER {
        println!("bits 16\n");
    }

    while let Ok(2) = reader.read(&mut mov_bytes) {
        let byte_1 = mov_bytes[0];
        let byte_2 = mov_bytes[1];

        assert_eq!(byte_1 >> 2, 0b100010); // assert it is register/memory to/from
                                           // register move
        assert_eq!(byte_2 >> 6, 0b11); // assert register to register mode

        // instruction operates on word data otherwise byte data.
        let w = match byte_1 & 0x00000001 {
            1 => true,
            0 => false,
            _ => unreachable!(),
        };

        // reg field is destination register
        let d = match byte_1 & 0x00000010 {
            1 => true,
            0 => false,
            _ => unreachable!(),
        };

        // extract reg field from 2nd byte
        let reg: u8 = (byte_2 & 0b00111000) >> 3;

        // extract r/m field from 2nd byte
        let r_m: u8 = byte_2 & 0b00000111;

        // source register
        let src = if d { r_m } else { reg };

        // destination register
        let dst = if d { reg } else { r_m };

        println!(
            "{}",
            format!("mov {}, {}", register_name(dst, w), register_name(src, w))
        );
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
