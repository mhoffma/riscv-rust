#![allow(unused)]
use bitmatch::bitmatch;

#[repr(u8)]
#[derive(Debug)]
enum Regno {
 X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,
 X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31
}
impl From<u8> for Regno {
    fn from(x: u8) -> Regno {
        unsafe { std::mem::transmute(x & 0b11111) }
    }
}
impl From<u32> for Regno {
    fn from(x: u32) -> Regno {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum Cbranch {
 Beq, Bne, E0, E1, Blt,Bge,Bltu,Bgeu
}
impl From<u32> for Cbranch {
    fn from(x: u32) -> Cbranch {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum LoadOp {
 Lb, Lh, Lw, Lbu, Lbh
}
impl From<u32> for LoadOp {
    fn from(x: u32) -> LoadOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum StoreOp {
 Sb, Sh, Sw,
}
impl From<u32> for StoreOp {
    fn from(x: u32) -> StoreOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum AluIOp {
   AddI, Slli, Slti, Sltiu,
   Xori, Srli, Ori,  Andi,
   E0, E1, E2, E3,
   E4, Srai
}
impl From<u32> for AluIOp {
    fn from(x: u32) -> AluIOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b1111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum AluOp {
   Add,Sll,Slt,Sltu,
   Xor,Srl,Or,And,
   Sub,E0,E1,E2,
   E3,Sra
}
impl From<u32> for AluOp {
    fn from(x: u32) -> AluOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b1111) }
    }
}

#[repr(u8)]
#[derive(Debug)]
enum MulOp {
     Mul,Mulh,Mulhsu,Mulhu,
     Div,Divu,Rem,Remu
}
impl From<u32> for MulOp {
    fn from(x: u32) -> MulOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b111) }
    }
}


#[repr(u8)]
#[derive(Debug)]
enum CsrOp {
   Ecall,Csrrw,Csrrs,E0,
   Csrrwi,Csrrsi,Csrrci,
   Ebreak
}
impl From<u32> for CsrOp {
    fn from(x: u32) -> CsrOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b1111) }
    }
}


#[repr(u8)]
#[derive(Debug)]
enum AmoOp {
Amoaddw,Amoswapw,Lrw,Scw,
Amoxorw,E5,E6,E7,
Amoorw,E9,E10,E11,
Amoandw,E13,E14,E15,
Amominw,E17,E18,E19,
Amomaxw,E21,E22,E23,
Amominuw,E25,E26,E27,
Amonmaxuw
}
impl From<u32> for AmoOp {
    fn from(x: u32) -> AmoOp {
        unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
    }
}

enum RegImm {
    R(Regno),
    I(u32)
}

#[derive(Debug)]
enum RiscvOP {
  Lui(u32),
  Auipc(u32),
  Jal(u32),
  Jalr(Regno,u32),
  Fencei,
  Branch(Cbranch,Regno,Regno,u32),
  Load(LoadOp,Regno,Regno,u32),
  Store(StoreOp,Regno,Regno,u32),
  AluI(AluIOp,Regno,Regno,u32),
  Alu(AluOp,Regno,Regno,Regno),
  Csr(CsrOp,Regno,Regno,u32),
  Mul(MulOp,Regno,Regno,Regno),
  Amo(AmoOp,Regno,Regno,Regno),
  None
}

#[bitmatch]
fn decode(inst: u32) -> RiscvOP {
    use RiscvOP::*;
    #[bitmatch]
    match inst {
    // J uuuuuuu uuuuu uuuuu uuu ddddd ooooo 11    
	"uuuuuuu uuuuu uuuuu uuu ddddd 01101 11" => Lui(u),
	"uuuuuuu uuuuu uuuuu uuu ddddd 00101 11" => Auipc(u),
	"uuuuuuu uuuuu uuuuu uuu ddddd 11011 11" => Jal(u),
	"uuuuuuu uuuuu uuuuu uuu ddddd 11001 11" => Jalr(d.into(),u),
	"uuuuuuu uuuuu uuuuu uuu ddddd 00011 11" => Fencei,
    // B iiiiiii bbbbb aaaaa fff iiiii ooooo 11
	"iiiiiii bbbbb aaaaa fff iiiii 11000 11" => Branch(f.into(),a.into(),b.into(),i),
    // I iiiiiii iiiii aaaaa fff ddddd ooooo 11
        "iiiiiii iiiii aaaaa fff ddddd 00000 11" => Load(f.into(),d.into(),a.into(),i),
        "iiiiiii iiiii aaaaa fff ddddd 01000 11" => Store(f.into(),d.into(),a.into(),i),
        "ifiiiii iiiii aaaaa fff ddddd 00100 11" => AluI(f.into(),d.into(),a.into(),i),
        "iiiiiii iiiif aaaaa fff ddddd 11100 11" => Csr(f.into(),d.into(),a.into(),i),	
    // R FFFFFFF bbbbb aaaaa fff ddddd ooooo 11
        "0f00000 bbbbb aaaaa fff ddddd ooooo 11" => Alu(f.into(),d.into(),a.into(),b.into()),
        "0000001 bbbbb aaaaa fff ddddd ooooo 11" => Mul(f.into(),d.into(),a.into(),b.into()),	
    // A FFFFFQL bbbbb aaaaa fff ddddd ooooo 11
        "FFFFFQL bbbbb aaaaa 010 ddddd 01011 11" => Amo(F.into(),d.into(),a.into(),b.into()),

	_ => RiscvOP::None
    }
}

#[test]
fn t0 () {
    let x: u32 = 0x80000537;
    let y = format!("{:?}", decode(x));
    //writeln!("{}",y);
    assert_eq!(y, "Lui(524288)");
}

fn main() {
   println!("{:?}", decode( 0x80000537));
   println!("{:?}", decode( 0xfe079ce3));
   println!("{:?}", decode( 0xff872683));
   println!("{:?}", decode( 0x00f72023));
   println!("{:?}", decode( 0x01010113));
   println!("{:?}", decode( 0x40d90933));
   println!("{:?}", decode( 0x13641073));
   println!("{:?}", decode( 0x03245433));      
   
}
