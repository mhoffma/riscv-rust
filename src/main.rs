#![allow(unused)]
use bitmatch::bitmatch;


macro_rules! fenum {
  ($ty:ident = { $( $enum:ident ),* } 
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

  (xxx $ty:ident = { $( $enum:ident ),* } ) => {
    fenum!{ @output $ty = {
            fenum!(@enumerate 0; [] $( $enum )*) } }
  };

  ( $ty:ident = { $( $enum:ident : $val:expr ),* } ) => {
    fenum!{ @output $ty = { $( $enum:$val ),* } }
  };

  ( @enumerate $i:expr ; [ $( $enum:ident : $val:expr )* ]) => {
    $( $enum:$val ),*
  };
  
  ( @enumerate $i:expr ; [ $( $enum:ident : $val:expr )* ] $e:ident $( $emore:ident )*) => { 
    fenum!(@enumerate $i+1; [$($enum:$val)* $e:$i] $($emore)*)
  };

  ( @output $ty:ident = { $( $enum:ident : $val:expr ),* } ) => {
    #[repr(u8)]
    #[derive(Debug)]
    enum $ty {
      $( $enum = $val ),*
    }
    impl From<u32> for $ty {
        fn from(x: u32) -> $ty {
           unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
        }
    }
  }
}


macro_rules! fimm {
    ($val:expr; [$($m:literal:$l:literal)*])    => { fimm!(@ false,false, $val; [$($m:$l)*]) };
    ($val:expr; sx[$($m:literal:$l:literal)*])  => { fimm!(@ false,true,  $val; [$($m:$l)*]) };    
    ($val:expr; dbg [$($m:literal:$l:literal)*])    => { fimm!(@ true,false, $val; [$($m:$l)*]) };
    ($val:expr; dbg sx[$($m:literal:$l:literal)*])  => { fimm!(@ true,true,  $val; [$($m:$l)*]) };    

    // reverse input before starting @fe state
    (@ $dbg:literal, $sx:literal, $val:expr; [] $($m:literal:$l:literal)*) => {
        fimm!(@fe $dbg,$sx,$val,0 ; $($m:$l)* ) // base case
    };
    (@ $dbg:literal,$sx:literal,$val:expr; [$m:literal:$l:literal $($m0:literal:$l0:literal)*]
     $($mr:literal:$lr:literal)*) => { 
        fimm!(@ $dbg,$sx,$val; [$($m0:$l0)*] $m:$l $($mr:$lr)*)  // recursion
    };

    (@fe $dbg:literal,$sx:literal,$val:expr,$pos:expr ; $m:literal:$l:literal) => {
        fimm!(@field $dbg,$sx,$val,$pos; $m:$l)
    };
    (@fe $dbg:literal,$sx:literal,$val:expr,$pos:expr ; $m:literal:$l:literal $($rest_m:literal:$rest_l:literal)*) => {
        fimm!(@field $dbg,false,$val,$pos; $m:$l) |
        fimm!(@fe $dbg,$sx,$val,$pos+($m-$l)+1 ; $($rest_m:$rest_l)*)
    };

    // @field signext, val, pos; p:sz
    (@field $dbg:literal,$sx:literal,$val:expr,$pos:expr; $m:literal:$l:literal) => {
      {
        let sz= $m-$l+1;
        let p = $l;
	let mask=((1<<sz)-1);
	let v = (($val&(mask<<$pos))>>$pos)<<p;
	let _m :u32 = ((!((1_u64<<($m+1))-1))) as u32;
	let o =	if $sx { v }
		else { v };
	
        if $dbg {
          println!("pos={:2} ({:2}:{:2}) mask={:032b} place={:032b} {:032b}",$pos,p,sz,
 	           (1<<sz)-1, ((1<<sz)-1)<<p, o)
        };
	o
      }
    }
}

macro_rules! imm {
    ($val:expr; $($k:ident)* [$($m:literal:$l:literal)*])    => {
       {
         let v=fimm!( $val ; $($k)* [$($m:$l)*]);
	 if false {
            println!("imm --> {:032b} ==> {} {:032b}",$val,stringify!($($m:$l)|*),v);
	    println!("{} == {}",$val,v);
	 }
	 v
       }
    }
}

#[test]
fn f0() {
   assert_eq!(fimm!(0x80000537; [31:12]),0x80000);
}

fenum!{Regno = { X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,
	         X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31 } }

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


fenum!{ CsrOp  = {
   Ecall:0,Csrrw:1,Csrrs:2,
   Csrrwi:3,Csrrsi:4,Csrrci:5,
   Ebreak:6
  }
}

fenum!{ AmoOp = {
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
	"uuuuuuu uuuuu uuuuu uuu ddddd 01101 11" => Lui(          imm!(u; [31:12])),
	"uuuuuuu uuuuu uuuuu uuu ddddd 00101 11" => Auipc(        imm!(u; [31:12])),
	"uuuuuuu uuuuu uuuuu uuu ddddd 11011 11" => Jal(          imm!(u; [20:20 10:1 11:11 19:12])),
	"uuuuuuu uuuuu uuuuu uuu ddddd 11001 11" => Jalr(d.into(),imm!(u;[11:0])),
	"uuuuuuu uuuuu uuuuu uuu ddddd 00011 11" => Fencei,
	"iiiiiii bbbbb aaaaa fff iiiii 11000 11" => Branch(f.into(),a.into(),b.into(),imm!(i; sx[12:12 10:5 4:1 11:11])),
        "iiiiiii iiiii aaaaa fff ddddd 00000 11" => Load(f.into(),d.into(),a.into(),  imm!(i;[11:0])),
        "iiiiiii iiiii aaaaa fff ddddd 01000 11" => Store(f.into(),d.into(),a.into(), imm!(i;[11:0])),
        "ifiiiii iiiii aaaaa fff ddddd 00100 11" => AluI(f.into(),d.into(),a.into(),  imm!(i;[11:0])),
        "iiiiiii iiiif aaaaa fff ddddd 11100 11" => Csr(f.into(),d.into(),a.into(),   imm!(i;[11:0])),
        "0f00000 bbbbb aaaaa fff ddddd ooooo 11" => Alu(f.into(),d.into(),a.into(),b.into()),
        "0000001 bbbbb aaaaa fff ddddd ooooo 11" => Mul(f.into(),d.into(),a.into(),b.into()),	
        "fffffql bbbbb aaaaa 010 ddddd 01011 11" => Amo(f.into(),d.into(),a.into(),b.into()),
	_ => RiscvOP::None
    }
}

#[test]
fn t0 () {
    assert_eq!("Lui(2147483648)",format!("{:?}",decode(0x80000537)));
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
   println!("{:?}", decode( 0x12450513));
}
