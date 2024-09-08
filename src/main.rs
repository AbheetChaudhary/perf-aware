use std::io::Read;
use std::fs::File;
use std::collections::HashMap;

const OPCODE_MASK: u8 = 0b11111100;
const   MODE_MASK: u8 = 0b11000000;
const    REG_MASK: u8 = 0b00111000;
const     RM_MASK: u8 = 0b00000111;
const      D_MASK: u8 = 0b00000010;
const      W_MASK: u8 = 0b00000001;
const     TWO_LSB: u8 = 0b00000001;

/// Refer Table 4-9. REG Field Encoding of 8086 Manual
const REG_LUT: [[&'static str; 8]; 2] = [
    ["al", "cl", "dl", "bl", "ah", "ch", "dh", "bh"],
    ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"]
];

macro_rules! reg_name_lut {
    ($w:ident, $reg:ident) => {{
        REG_LUT[$w as usize][$reg as usize]
    }}
}

/// Refer Table 4-10. R/M Field Encoding of 8086 Manual
const EAC_LUT: [&'static str; 8] = [
    "bx + si",
    "bx + di",
    "bp + si",
    "bp + di",
    "si",
    "di",
    "bp",
    "bx",
];

macro_rules! eac_base_index_lut {
    ($rm:ident) => {{
        EAC_LUT[$rm as usize]
    }}
}

macro_rules! size_specifier {
    (&$w:ident) => {{
        match &$w {
            &0b0 => "byte",
            &0b1 => "word",
            _ => unreachable!(),
        }
    }}
}

const MEM_MODE_00: u8 = 0b00; // Memory mode, no displacement follows. Except
                              // when R/M = 0b110, then 16-bit displacement.
const MEM_MODE_08: u8 = 0b01; // Memory mode, 8-bit displacement follows.
const MEM_MODE_16: u8 = 0b10; // Memory mode, 16-bit displacement follows.
const    REG_MODE: u8 = 0b11; // Register mode, no displacement.

/// Get d field as boolean.
macro_rules! get_d {
    ($byte:ident) => {{
        match $byte & D_MASK {
            0b10 => true,
            0b00 => false, 
            _ => unreachable!(),
        }
    }}
}

/// Get next byte from byte_stream or panic.
macro_rules! get_next_or_panic {
    (&mut $stream:ident) => {{
        match $stream.get_next() {
            Some(byte) => byte,
            None => {
                dbg!(&$stream);
                panic!("Not a single byte to read.");
            }
        }
    }}
}

/// Get next two bytes from byte_stream or panic.
macro_rules! get_next_two_or_panic {
    (&mut $stream:ident) => {{
        let first = get_next_or_panic!(&mut $stream);
        let second = get_next_or_panic!(&mut $stream);
        (first, second)
    }}
}

type InstAddr = usize; // Index of the byte where an instruction begins.
type Label = String; // Labels are names associated to some InstAddr's.

struct ByteStream {
    /// An iterator of remaining bytes in the byte stream.
    remaining: Box<dyn Iterator<Item = u8>>,

    /// Number of complete instructions that has already been processed.
    inst_count: usize,

    /// Number of bytes that has already been read. A fractional number of
    /// instructions could have been processed for some byte_count values.
    byte_count: usize,

    /// Instructions in assembly and its beginning index in the binary.
    instructions: Vec<(String, InstAddr)>,

    /// All the identified labels and addresses of the associated instructions.
    labels: HashMap<InstAddr, Label>,
}

impl ByteStream {
    fn new(stream: Vec<u8>) -> Self {
        ByteStream {
            remaining: Box::new(stream.into_iter()),
            inst_count: 0,
            byte_count: 0,
            instructions: vec![],
            labels: HashMap::new(),
        }
    }

    /// Get next byte in byte stream.
    fn get_next(&mut self) -> Option<u8> {
        match self.remaining.next() {
            Some(byte) => {
                self.byte_count += 1;
                Some(byte)
            }
            None => None
        }
    }

    /// Add assembly of newly decoded instruction and its index/addr from
    /// binary.
    fn add_inst_string(&mut self, asm: String, addr: InstAddr) {
        self.inst_count += 1;
        self.instructions.push((asm, addr));
    }
}

/// One liner for handling jump/loop like instructions with a label.
macro_rules! inst_with_label {
    (&mut $stream:ident, &$inst_begin:ident, $operation:literal) => {{
        // 8-bit signed increment to instruction pointer.
        let inc8 = get_next_or_panic!(&mut $stream) as i8;
        
        // Address of the instruction after jump.
        let jump_addr = if inc8 < 0 {
            let temp = inc8.unsigned_abs() as usize;
            assert!($stream.byte_count >= temp);
            $stream.byte_count - temp 
        } else {
            $stream.byte_count + inc8 as usize
        };

        // Get existing label associated to jump_addr or create new one.
        let label = match $stream.labels.get(&jump_addr) {
            Some(label) => label.clone(),
            None => {
                let label = format!("label_{:02}", $stream.labels.len());
                $stream.labels.insert(jump_addr, label.clone());
                label
            }
        };

        $stream.add_inst_string(
            format!("{} {label}", $operation),
            $inst_begin,
        );
    }}
}

use std::fmt;
impl fmt::Debug for ByteStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Completely processed instructuons: {}",
            self.inst_count
        )?;
        match self.inst_count {
            0 => writeln!(f, "Last instruction string: Nil")?,
            n => writeln!(f, "Last instruction string: {}",
                &self.instructions[n-1].0)?,
        }
        writeln!(f, "Bytes read: {}", self.byte_count)?;
        writeln!(f, "Labels identified: {}", self.labels.len())
    }
}

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<String>>();
    if args.len() != 2 {
        eprintln!("usage: {} <binary-filename>", &args[0]);
        std::process::exit(-1);
    }

    let mut file = File::open(&args[1])?;

    let mut bytes = vec![];

    file.read_to_end(&mut bytes)?;

    let mut byte_stream = ByteStream::new(bytes);

    while let Some(first) = byte_stream.get_next() {
        // InstAddr of the current instruction being processes.
        let inst_begin = byte_stream.byte_count - 1;

        let opcode = (first & OPCODE_MASK) >> 2;

        match opcode {
            // MOV = Move

            // MOV: Register/memory to/from register.
            0b100010 => {
                let w = first & W_MASK;
                let d = get_d!(first);

                let second = get_next_or_panic!(&mut byte_stream);
                let mode = (second & MODE_MASK) >> 6;
                let reg = (second & REG_MASK) >> 3;
                let rm = second & RM_MASK;

                if mode == REG_MODE {
                    let (src, dst) = if d {
                        (reg_name_lut!(w, rm), reg_name_lut!(w, reg))
                    } else {
                        (reg_name_lut!(w, reg), reg_name_lut!(w, rm))
                    };

                    byte_stream.add_inst_string(
                        format!("mov {}, {}", dst, src),
                        inst_begin
                    );
                } else if mode == MEM_MODE_00 {
                    if rm == 0b110 /* Direct Addressing */ {
                        let (disp_lo, disp_hi) =
                            get_next_two_or_panic!(&mut byte_stream);
                        let direct_addr =
                            ((disp_hi as u16) << 8) | (disp_lo as u16);

                        if d {
                            let dst = reg_name_lut!(w, reg);
                            
                            byte_stream.add_inst_string(
                                format!("mov {}, [{}]", dst, direct_addr),
                                inst_begin
                            );
                        } else {
                            let src = reg_name_lut!(w, reg);
                            
                            byte_stream.add_inst_string(
                                format!("mov [{}], {}", direct_addr, src),
                                inst_begin
                            );
                        }
                    } else {
                        if d {
                            assert!(rm != 0b110);
                            let src = eac_base_index_lut!(rm);

                            let dst = reg_name_lut!(w, reg);

                            byte_stream.add_inst_string(
                                format!("mov {}, [{}]", dst, src),
                                inst_begin
                            );
                        } else {
                            let src = reg_name_lut!(w, reg);

                            assert!(rm != 0b110);
                            let dst = eac_base_index_lut!(rm);

                            byte_stream.add_inst_string(
                                format!("mov [{}], {}", dst, src),
                                inst_begin
                            );
                        };

                    }
                } else if mode == MEM_MODE_08 {
                    let disp_lo = get_next_or_panic!(&mut byte_stream);
                    let disp = (disp_lo as i8) as i16;

                    if d {
                        let src = eac_base_index_lut!(rm);
                        let dst = reg_name_lut!(w, reg);

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov {dst}, [{src} - {}]",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                            0 => byte_stream.add_inst_string(
                                format!("mov {dst}, [{src}]"),
                                inst_begin
                            ),
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("mov {dst}, [{src} + {}]", disp),
                                    inst_begin
                                );
                            }
                        }
                    } else {
                        let src = reg_name_lut!(w, reg);
                        let dst = eac_base_index_lut!(rm);

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov [{dst} - {}], {src}",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                            0 => byte_stream.add_inst_string(
                                format!("mov [{dst}], {src}"),
                                inst_begin
                            ),
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov [{dst} + {}], {src}",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                        }
                    }
                } else if mode == MEM_MODE_16 {
                    let (disp_lo, disp_hi) =
                        get_next_two_or_panic!(&mut byte_stream);
                    let disp =
                        ((disp_hi as u16) << 8) as i16 
                        | ((disp_lo as u16) as i16);

                    if d {
                        let src = eac_base_index_lut!(rm);
                        let dst = reg_name_lut!(w, reg);

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov {dst}, [{src} - {}]",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                            0 => byte_stream.add_inst_string(
                                format!("mov {dst}, [{src}]"),
                                inst_begin
                            ),
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("mov {dst}, [{src} + {}]", disp),
                                    inst_begin
                                );
                            }
                        }
                    } else {
                        let src = reg_name_lut!(w, reg);
                        let dst = eac_base_index_lut!(rm);
                        
                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov [{dst} - {}], {src}",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                            0 => byte_stream.add_inst_string(
                                format!("mov [{dst}], {src}"),
                                inst_begin
                            ),
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "mov [{dst} + {}], {src}",
                                        disp.abs()
                                    ),
                                    inst_begin
                                );
                            }
                        }
                    }

                } else {
                    unreachable!();
                }
            }

            // MOV: Immediate to register/memory.
            0b110001 if first & D_MASK == 0b00000010 => {
                let w = first & W_MASK;
                
                let second = get_next_or_panic!(&mut byte_stream);
                let mode = (second & MODE_MASK) >> 6;
                let rm = second & RM_MASK;

                if mode == REG_MODE {
                    let dst = reg_name_lut!(w, rm);
                    let immed = if w == 0b1 {
                        let (immed_lo, immed_hi) =
                            get_next_two_or_panic!(&mut byte_stream);
                        let immed16 =
                            ((immed_hi as u16) << 8) | immed_lo as u16;
                        immed16
                    } else if w == 0b0 {
                        let immed8 = get_next_or_panic!(&mut byte_stream);
                        immed8 as u16
                    } else {
                        unreachable!();
                    };

                    byte_stream.add_inst_string(
                        format!("mov {dst}, {immed}"),
                        inst_begin
                    );

                } else if mode == MEM_MODE_00 {
                    if rm == 0b110 /* Direct Addressing */ {
                        let (disp_lo, disp_hi) =
                            get_next_two_or_panic!(&mut byte_stream);
                        let direct_addr =
                            ((disp_hi as u16) << 8) | (disp_lo as u16);

                        let immed = if w == 0b1 {
                            let (immed_lo, immed_hi) =
                                get_next_two_or_panic!(&mut byte_stream);
                            let immed16 =
                                ((immed_hi as u16) << 8) | immed_lo as u16;
                            immed16
                        } else if w == 0b0 {
                            let immed8 = get_next_or_panic!(&mut byte_stream);
                            immed8 as u16
                        } else {
                            unreachable!();
                        };

                        let opsize = size_specifier!(&w);

                        byte_stream.add_inst_string(
                            format!("mov {opsize} [{direct_addr}], {immed}"),
                            inst_begin
                        );

                    } else {
                        let dst = eac_base_index_lut!(rm);
                        let immed = if w == 0b1 {
                            let (immed_lo, immed_hi) = 
                                get_next_two_or_panic!(&mut byte_stream);
                            let immed16 =
                                ((immed_hi as u16) << 8) | immed_lo as u16;
                            immed16
                        } else if w == 0b0 {
                            let immed8 = get_next_or_panic!(&mut byte_stream);
                            immed8 as u16
                        } else {
                            unreachable!();
                        };

                        let opsize = size_specifier!(&w);

                        byte_stream.add_inst_string(
                            format!("mov {opsize} [{dst}], {immed}"), 
                            inst_begin
                        );
                    }
                } else if mode == MEM_MODE_08 {
                    let disp_lo = get_next_or_panic!(&mut byte_stream);
                    let disp = (disp_lo as i8) as i16;
                    let immed = if w == 0b1 {
                        let (immed_lo, immed_hi) = 
                            get_next_two_or_panic!(&mut byte_stream);
                        let immed16 =
                            ((immed_hi as u16) << 8) | immed_lo as u16;
                        immed16
                    } else if w == 0b0 {
                        let immed8 = get_next_or_panic!(&mut byte_stream);
                        immed8 as u16
                    } else {
                        unreachable!();
                    };

                    let dst = eac_base_index_lut!(rm);

                    let opsize = size_specifier!(&w);

                    match disp {
                        i16::MIN..=-1 => {
                            byte_stream.add_inst_string(
                                format!(
                                    "mov {opsize} [{dst} - {}], {immed}",
                                    disp.abs()
                                ),
                                inst_begin
                            );
                        }
                        0 => byte_stream.add_inst_string(
                            format!("mov {opsize} [{dst}], {immed}"),
                            inst_begin
                        ),
                        1.. => {
                            byte_stream.add_inst_string(
                                format!(
                                    "mov {opsize} [{dst} + {}], {immed}",
                                    disp
                                ),
                                inst_begin
                            );
                        }
                    }
                } else if mode == MEM_MODE_16 {
                    let (disp_lo, disp_hi) = 
                        get_next_two_or_panic!(&mut byte_stream);
                    let disp =
                        ((disp_hi as u16) << 8) as i16 
                        | ((disp_lo as u16) as i16);
                    let immed = if w == 0b1 {
                        let (immed_lo, immed_hi) = 
                            get_next_two_or_panic!(&mut byte_stream);
                        let immed16 =
                            ((immed_hi as u16) << 8) | immed_lo as u16;
                        immed16
                    } else if w == 0b0 {
                        let immed8 = get_next_or_panic!(&mut byte_stream);
                        immed8 as u16
                    } else {
                        unreachable!();
                    };

                    let dst = eac_base_index_lut!(rm);

                    let opsize = size_specifier!(&w);

                    match disp {
                        i16::MIN..=-1 => {
                            byte_stream.add_inst_string(
                                format!(
                                    "mov {opsize} [{dst} - {}], {immed}",
                                    disp.abs()
                                ),
                                inst_begin
                            );
                        }
                        0 => byte_stream.add_inst_string(
                            format!("mov {opsize} [{dst}], {immed}"), 
                            inst_begin
                        ),
                        1.. => {
                            byte_stream.add_inst_string(
                                format!(
                                    "mov {opsize} [{dst} + {}], {immed}",
                                    disp
                                ),
                                inst_begin
                            );
                        }
                    }

                } else {
                    unreachable!();
                }
            }

            // MOV: Immediate to register.
            _ if first & 0b11110000 == 0b10110000 => {
                let reg = first & 0b00000111;
                let w = (first & 0b00001000) >> 3;
                let dst = reg_name_lut!(w, reg);
                let immed = if w == 0b1 {
                    let (immed_lo, immed_hi) =
                        get_next_two_or_panic!(&mut byte_stream);
                    let immed16 = ((immed_hi as u16) << 8) | (immed_lo as u16);
                    immed16
                } else {
                    let immed_lo = get_next_or_panic!(&mut byte_stream);
                    immed_lo as u16
                };

                byte_stream.add_inst_string(
                    format!("mov {dst}, {immed}"),
                    inst_begin
                );
            }

            // MOV: Memory to accumulator.
            _ if first & 0b11111110 == 0b10100000 => {
                let (addr_lo, addr_hi) = 
                    get_next_two_or_panic!(&mut byte_stream);
                let addr = ((addr_hi as u16) << 8) | (addr_lo as u16);
                let w = first & W_MASK;

                let opsize = size_specifier!(&w);
                byte_stream.add_inst_string(
                    format!("mov ax, {opsize} [{}]", addr),
                    inst_begin
                );
            }

            // MOV: Accumulator to memory.
            _ if first & 0b11111110 == 0b10100010 => {
                let (addr_lo, addr_hi) =
                    get_next_two_or_panic!(&mut byte_stream);
                let addr = ((addr_hi as u16) << 8) | (addr_lo as u16);
                let w = first & W_MASK;

                let opsize = size_specifier!(&w);
                byte_stream.add_inst_string(
                    format!("mov {opsize} [{addr}], ax"),
                    inst_begin
                );
            }

            // MOV: Register/memory to segment register. TODO
            // MOV: Segment register to register/memory. TODO

            // ADD | SUB | CMP: Reg/memory with register to either.
            0b000000 /* ADD */ | 0b001010 /* SUB */ | 0b001110 /* CMP */ => {
                // Operation name.
                let operation = if opcode == 0b000000 {
                    "add"
                } else if opcode == 0b001010 {
                    "sub"
                } else {
                    "cmp"
                };

                let w = first & W_MASK;
                let d = get_d!(first);

                let second = get_next_or_panic!(&mut byte_stream);
                let mode = (second & MODE_MASK) >> 6;
                let reg = (second & REG_MASK) >> 3;
                let rm = second & RM_MASK;

                if mode == REG_MODE {
                    let (src, dst) = if d {
                        (reg_name_lut!(w, rm), reg_name_lut!(w, reg))
                    } else {
                        (reg_name_lut!(w, reg), reg_name_lut!(w, rm))
                    };

                    byte_stream.add_inst_string(
                        format!("{operation} {dst}, {src}"),
                        inst_begin
                    );
                } else if mode == MEM_MODE_00 {
                    if rm == 0b110 /* Direct Addressing */ {
                        let (disp_lo, disp_hi) =
                            get_next_two_or_panic!(&mut byte_stream);
                        let direct_addr =
                            ((disp_hi as u16) << 8) | (disp_lo as u16);
                        let opsize = size_specifier!(&w);

                        if d {
                            let dst = reg_name_lut!(w, reg);
                            byte_stream.add_inst_string(
                                format!("{operation} {dst}, {opsize} \
                                    [{direct_addr}]"),
                                inst_begin
                            );
                        } else {
                            let src = reg_name_lut!(w, reg);
                            byte_stream.add_inst_string(
                                format!("{operation} {opsize} \
                                    [{direct_addr}], {src}"),
                                inst_begin,
                            );
                        }
                    } else {
                        let opsize = size_specifier!(&w);

                        if d {
                            let src = eac_base_index_lut!(rm);
                            let dst = reg_name_lut!(w, reg);
                            byte_stream.add_inst_string(
                                format!("{operation} {dst}, {opsize} [{src}]"),
                                inst_begin
                            );
                        } else {
                            let src = reg_name_lut!(w, reg);
                            let dst = eac_base_index_lut!(rm);
                            byte_stream.add_inst_string(
                                format!("{operation} {opsize} [{dst}], {src}"),
                                inst_begin
                            );
                        }
                    }
                } else {
                    let disp = if mode == MEM_MODE_08 {
                        let disp_lo = get_next_or_panic!(&mut byte_stream);
                        (disp_lo as i8) as i16
                    } else if mode == MEM_MODE_16 {
                        let (disp_lo, disp_hi) = 
                            get_next_two_or_panic!(&mut byte_stream);
                        let disp = 
                            ((disp_hi as u16) << 8) as i16 
                            | ((disp_lo as u16) as i16);
                        disp
                    } else {
                        unreachable!();
                    };

                    let opsize = size_specifier!(&w);

                    if d {
                        let src = eac_base_index_lut!(rm);
                        let dst = reg_name_lut!(w, reg);

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {dst}, {opsize} \
                                        [{src} - {}]", disp.abs()),
                                    inst_begin,
                                );
                            }
                            0 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {dst}, {opsize} \
                                        [{src}]"),
                                    inst_begin
                                );
                            }
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {dst}, {opsize} \
                                        [{src} + {disp}]"),
                                    inst_begin,
                                );
                            }
                        }
                    } else {
                        let src = reg_name_lut!(w, reg);
                        let dst = eac_base_index_lut!(rm);

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {opsize} \
                                        [{dst} - {}], {src}", disp.abs()),
                                    inst_begin,
                                );
                            }
                            0 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {opsize} \
                                        [{dst}], {src}"),
                                    inst_begin
                                );
                            }
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("{operation} {opsize} \
                                        [{dst} + {disp}], {src}"),
                                    inst_begin,
                                );
                            }
                        }
                    }
                }
            }
            
            // ADD | SUB | CMP: Immediate with register/memory.
            0b100000 => {
                let w = first & W_MASK;
                let s = get_d!(first);

                let second = get_next_or_panic!(&mut byte_stream);
                let mode = (second & MODE_MASK) >> 6;
                let reg = (second & REG_MASK) >> 3;
                let rm = second & RM_MASK;

                // Operation name.
                let operation = match reg {
                    0b000 => "add",
                    0b101 => "sub",
                    0b111 => "cmp",
                    _ => unreachable!(),
                };

                if mode == REG_MODE {
                    let dst = reg_name_lut!(w, rm);
                    if w == 0b0 {
                        // s does not matter when w = 0.
                        let immed = {
                            let immed8 = get_next_or_panic!(&mut byte_stream);
                            immed8
                        };

                        byte_stream.add_inst_string(
                            format!("{operation} {dst}, {immed}"),
                            inst_begin,
                        );
                    } else if w == 0b1 && !s {
                        let immed = {
                            let (immed_lo, immed_hi) =
                                get_next_two_or_panic!(&mut byte_stream);
                            let immed16 =
                                ((immed_hi as u16) << 8) | (immed_lo as u16);
                            immed16
                        };

                        byte_stream.add_inst_string(
                            format!("{operation} {dst}, {immed}"),
                            inst_begin,
                        );
                    } else if w == 0b1 && s {
                        let immed = {
                            let immed_lo = get_next_or_panic!(&mut byte_stream);
                            (immed_lo as i8) as i16
                        };
                        
                        byte_stream.add_inst_string(
                            format!("{operation} {dst}, {immed}"),
                            inst_begin,
                        );
                    }
                } else if mode == MEM_MODE_00 {
                    if rm == 0b110 /* Direct Addressing */ {
                        let (disp_lo, disp_hi) =
                            get_next_two_or_panic!(&mut byte_stream);
                        let direct_addr = ((disp_hi as u16) << 8) 
                            | (disp_lo as u16);

                        if w == 0b0 {
                            // s does not matter when w = 0.
                            let immed = {
                                let immed8 =
                                    get_next_or_panic!(&mut byte_stream);
                                immed8
                            };

                            byte_stream.add_inst_string(
                                format!("{operation} byte \
                                    [{direct_addr}], {immed}"),
                                inst_begin,
                            );
                        } else if w == 0b1 && !s {
                            let immed = {
                                let (immed_lo, immed_hi) = 
                                    get_next_two_or_panic!(&mut byte_stream);
                                let immed16 = ((immed_hi as u16) << 8) 
                                    | (immed_lo as u16);
                                immed16
                            };

                            byte_stream.add_inst_string(
                                format!("{operation} word \
                                    [{direct_addr}], {immed}"),
                                inst_begin,
                            );
                        } else if w == 0b1 && s {
                            let immed = {
                                let immed_lo = 
                                    get_next_or_panic!(&mut byte_stream);
                                (immed_lo as i8) as i16
                            };
                            
                            byte_stream.add_inst_string(
                                format!("{operation} word \
                                    [{direct_addr}], {immed}"),
                                inst_begin,
                            );
                        }
                    } else {
                        let dst = eac_base_index_lut!(rm);
                        if w == 0b0 {
                            // s does not matter when w = 0.
                            let immed = {
                                let immed8 = 
                                    get_next_or_panic!(&mut byte_stream);
                                immed8
                            };

                            byte_stream.add_inst_string(
                                format!("{operation} byte [{dst}], {immed}"),
                                inst_begin,
                            );
                        } else if w == 0b1 && !s {
                            let immed = {
                                let (immed_lo, immed_hi) = 
                                    get_next_two_or_panic!(&mut byte_stream);
                                let immed16 = ((immed_hi as u16) << 8) 
                                    | (immed_lo as u16);
                                immed16
                            };

                            byte_stream.add_inst_string(
                                format!("{operation} word [{dst}], {immed}"),
                                inst_begin,
                            );
                        } else if w == 0b1 && s {
                            let immed = {
                                let immed_lo = 
                                    get_next_or_panic!(&mut byte_stream);
                                (immed_lo as i8) as i16
                            };
                            
                            byte_stream.add_inst_string(
                                format!("{operation} word [{dst}], {immed}"),
                                inst_begin,
                            );
                        }
                    }
                } else {
                    let disp = if mode == MEM_MODE_08 {
                        let disp_lo = get_next_or_panic!(&mut byte_stream);
                        (disp_lo as i8) as i16
                    } else if mode == MEM_MODE_16 {
                        let (disp_lo, disp_hi) = 
                            get_next_two_or_panic!(&mut byte_stream);
                        let disp = ((disp_hi as u16) << 8) as i16 
                            | ((disp_lo as u16) as i16);
                        disp
                    } else {
                        unreachable!();
                    };

                    let dst = eac_base_index_lut!(rm);

                    if w == 0b0 {
                        // s does not matter when w = 0.
                        let immed = {
                            let immed8 = get_next_or_panic!(&mut byte_stream);
                            immed8
                        };

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} byte [{dst} + {}], \
                                        {immed}", disp.abs()),
                                    inst_begin,
                                );
                            }
                            0 => {
                                byte_stream.add_inst_string(
                                    format!(
                                        "{operation} byte [{dst}], {immed}"
                                    ),
                                    inst_begin,
                                );
                            }
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("{operation} byte \
                                        [{dst} + {disp}], {immed}"),
                                    inst_begin
                                );
                            }
                        }
                    } else if w == 0b1 && !s {
                        let immed = {
                            let (immed_lo, immed_hi) =
                                get_next_two_or_panic!(&mut byte_stream);
                            let immed16 =
                                ((immed_hi as u16) << 8) | (immed_lo as u16);
                            immed16
                        };

                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word [{dst} + {}], \
                                        {immed}", disp.abs()),
                                    inst_begin,
                                );
                            }
                            0 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word \
                                        [{dst}], {immed}"),
                                    inst_begin,
                                );
                            }
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word \
                                        [{dst} + {disp}], {immed}"),
                                    inst_begin
                                );
                            }
                        }
                    } else if w == 0b1 && s {
                        let immed = {
                            let immed_lo = get_next_or_panic!(&mut byte_stream);
                            (immed_lo as i8) as i16
                        };
                        
                        match disp {
                            i16::MIN..=-1 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word \
                                        [{dst} + {}], {immed}", disp.abs()),
                                    inst_begin,
                                );
                            }
                            0 => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word \
                                        [{dst}], {immed}"),
                                    inst_begin,
                                );
                            }
                            1.. => {
                                byte_stream.add_inst_string(
                                    format!("{operation} word \
                                        [{dst} + {disp}], {immed}"),
                                    inst_begin
                                );
                            }
                        }
                    }
                }
            } 

            // ADD: Immediate to accumulator.
            0b000001 if first & 0b00000010 == 0b0 => {
                let w = first & W_MASK;
                if w == 0b1 {
                    let (immed_lo, immed_hi) =
                        get_next_two_or_panic!(&mut byte_stream);
                    let immed16 = 
                        ((immed_hi as u16) << 8) | (immed_lo as u16);

                    byte_stream.add_inst_string(
                        format!("add ax, {immed16}"),
                        inst_begin,
                    );
                } else {
                    let immed8 = get_next_or_panic!(&mut byte_stream);
                    byte_stream.add_inst_string(
                        format!("add al, {immed8}"),
                        inst_begin,
                    );
                }
            }

            // SUB: Immediate from accumulator.
            0b001011 if first & 0b00000010 == 0b0 => {
                let w = first & W_MASK;
                if w == 0b1 {
                    let (immed_lo, immed_hi) =
                        get_next_two_or_panic!(&mut byte_stream);
                    let immed16 = ((immed_hi as u16) << 8) | (immed_lo as u16);

                    byte_stream.add_inst_string(
                        format!("sub ax, {immed16}"),
                        inst_begin,
                    );
                } else {
                    let immed8 = get_next_or_panic!(&mut byte_stream);
                    byte_stream.add_inst_string(
                        format!("sub al, {immed8}"),
                        inst_begin,
                    );
                }
            }

            // CMP: Immediate and accumulator.
            0b001111 if first & 0b00000010 == 0b0 => {
                let w = first & W_MASK;
                if w == 0b1 {
                    let (immed_lo, immed_hi) =
                        get_next_two_or_panic!(&mut byte_stream);
                    let immed16 = ((immed_hi as u16) << 8) | (immed_lo as u16);

                    byte_stream.add_inst_string(
                        format!("cmp ax, {immed16}"),
                        inst_begin,
                    );
                } else {
                    let immed8 = get_next_or_panic!(&mut byte_stream);
                    byte_stream.add_inst_string(
                        format!("cmp al, {immed8}"),
                        inst_begin,
                    );
                }
            }

            // JE/JZ
            0b011101 if first & TWO_LSB == 0b00 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "je"
            ),

            // JL/JNGE
            0b011111 if first & TWO_LSB == 0b00 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jl"
            ),

            // JLE/JNG
            0b111111 if first & TWO_LSB == 0b10 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jle"
            ),

            // JB/JNAE
            0b011100 if first & TWO_LSB == 0b10 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jb"
            ),

            // JP/JPE
            0b011110 if first & TWO_LSB == 0b10 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jp"
            ),

            // JO
            0b011100 if first & TWO_LSB == 0b00 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jo"
            ),

            // JS
            0b011110 if first & TWO_LSB == 0b00 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "js"
            ),

            // JNE/JNZ
            0b011101 if first & TWO_LSB == 0b01 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jne"
            ),

            // JNL/JGE
            0b011111 if first & TWO_LSB == 0b01 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jnl"
            ),

            // JNLE/JG
            0b011111 if first & TWO_LSB == 0b11 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jnle"
            ),

            // JNB/JAE
            0b011100 if first & TWO_LSB == 0b11 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jnb"
            ),

            // JNBE/JA
            0b011101 if first & TWO_LSB == 0b11 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jnbe"
            ),

            // JNP/JPO
            0b011110 if first & TWO_LSB == 0b11 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jnp"
            ),

            // JNO
            0b011100 if first & TWO_LSB == 0b01 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jno"
            ),

            // JNS
            0b011110 if first & TWO_LSB == 0b01 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jns"
            ),

            // LOOP
            0b111000 if first & TWO_LSB == 0b10 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "loop"
            ),

            // LOOPZ/LOOPE
            0b111000 if first & TWO_LSB == 0b01 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "loopz"
            ),

            // LOOPNZ/LOOPNE
            0b111000 if first & TWO_LSB == 0b00 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "loopnz"
            ),

            // JCXZ
            0b111000 if first & TWO_LSB == 0b11 => inst_with_label!(
                &mut byte_stream,
                &inst_begin,
                "jcxz"
            ),

            _ => {
                dbg!(&byte_stream);
                for (asm, _) in &byte_stream.instructions {
                    println!("{}", asm);
                }
                unreachable!(
                    "opcode: 0b{:0>6b}, first: 0b{:0>8b}",
                    opcode, first);
            }
        }
    }

    let label_addrs = byte_stream.labels.keys().collect::<Vec<&usize>>();

    // Start printing gathered assembly instruction strings.
    for (asm, begin) in &byte_stream.instructions {
        // Print the associated label before printing the instruction, if the
        // instruction has any associated label.
        match label_addrs.iter().find(|&&a| a == begin) {
            Some(addr) => println!(
                "\n{}:",
                byte_stream.labels.get(&addr).unwrap()
            ),
            None => {},
        }

        println!("{asm}");
    }

    Ok(())
}
