#![allow(unused)]
use bitmatch::bitmatch;

macro_rules! fenum {
  ( $ty:ident = { $( $enum:ident ),* } 
  ) => {
    #[repr(u8)]
    #[derive(Debug)]
    enum $ty {
      $( $enum, )*
    }
    impl From<u32> for $ty {
        fn from(x: u32) -> $ty {
           unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
        }
    }
  };
  
  ( $ty:ident = { $( $enum:ident : $val:expr ),* } 
  ) => {
    #[repr(u8)]
    #[derive(Debug)]
    enum $ty {
      $( $enum=$val, )*
    }
    impl From<u32> for $ty {
        fn from(x: u32) -> $ty {
           unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
        }
    }
  }
}

fenum!{Regno = {
	     X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,
	     X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31 }
	     }


fenum!{ Branch = { Beq:0, Bne:1,Blt:4,Bgt:5,Bltu:6,Bgeu:7 } }

fenum!{ LoadOp = { Lb, Lh, Lw, Lbu, Lbh } }

fenum!{ StoreOp = {  Sb, Sh, Sw } }

fenum!{ AluIOp = {
   AddI:0, Slli:1, Slti:2, Sltiu:3,
   Xori:4, Srli:5, Ori:6,  Andi:7,
   Srai:13
} }

fenum!{ AluOp = {
   Add:0,Sll:1,Slt:2,Sltu:3,
   Xor:4,Srl:5,Or:6,And:7,
   Sub:8,Sra:13
} }

fenum!{ MulOp = {
     Mul,Mulh,Mulhsu,Mulhu,
     Div,Divu,Rem,Remu
} }


fenum!{
  CsrOp  = {
   Ecall:0,Csrrw:1,Csrrs:2,
   Csrrwi:3,Csrrsi:4,Csrrci:5,
   Ebreak:6
  }
}

fenum!{
   AmoOp = {
     Amoaddw:0,Amoswapw:1,Lrw:2,Scw:3,
     Amoxorw:4,Amoorw:8,Amoandw:12,Amominw:16,
     Amomaxw:20,Amominuw:24,Amonmaxuw:28
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
  Branch(Branch,Regno,Regno,u32),
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
    assert_eq!("Lui(524288)",format!("{:?}",decode(0x80000537)));
    assert_eq!("Branch(Bne, X15, X0, 4089)",format!("{:?}",decode( 0xfe079ce3)));
    assert_eq!("Load(Lw, X13, X14, 4088)",format!("{:?}",decode(0xff872683)));
    assert_eq!("Store(Sw, X0, X14, 15)",format!("{:?}",decode(0x00f72023)));
    assert_eq!("AluI(AddI, X2, X2, 16)",format!("{:?}",decode(0x01010113)));
    assert_eq!("Alu(Sub, X18, X18, X13)",format!("{:?}",decode(0x40d90933)));
    assert_eq!("Csr(Csrrw, X0, X8, 155)",format!("{:?}",decode(0x13641073)));
    assert_eq!("Mul(Divu, X8, X8, X18)",format!("{:?}",decode(0x03245433)));
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
