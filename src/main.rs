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
      $( $enum = $val, )*
      Crap
    }
    impl From<u32> for $ty {
        fn from(x: u32) -> $ty {
           //unsafe { std::mem::transmute(u8::try_from(x).unwrap() & 0b11111) }
	   use $ty::*;
	   match x {
	      $($val => $enum,)*
	      _ => Crap
	   }
        }
    }
  }
}


macro_rules! fimm {
    ($val:expr; [$($m:literal:$l:literal)*])    => { fimm!(@ false,false, $val; [$($m:$l)*]) };
    ($val:expr; nzuimm [$($m:literal:$l:literal)*])  => { fimm!(@ false,false,  $val; [$($m:$l)*]) };
    ($val:expr; nzimm [$($m:literal:$l:literal)*])  => { fimm!(@ false,false,  $val; [$($m:$l)*]) };
    ($val:expr; upper nzimm [$($m:literal:$l:literal)*])  => { fimm!(@ false,false,  $val; [$($m:$l)*])<<16 };
    ($val:expr; uimm [$($m:literal:$l:literal)*])  => { fimm!(@ false,false,  $val; [$($m:$l)*]) };    
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
	let o =	if $sx { v | _m}
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

// todo these need to really point to Regno X8=Regno::X8
fenum!{ Regno8 ={X8,X9,X10,X11,X12,X13,X14,X15} } 


#[derive(Debug)]
enum RiscvOpC {
     Add4spn(Regno,u32),
     Ldw(Regno8,u32),
     Addi(Regno,u32),
     Nop,
     Jal(u32),
     Addiw(Regno,u32),
     Li(Regno,u32),
     Addi16sp(u32),
     SrlI(Regno8,u32),
     SrlaI(Regno8,u32),
     AndI(Regno8,u32),
     Sub(Regno8,Regno8),
     Xor(Regno8,Regno8),
     Ior(Regno8,Regno8),
     And(Regno8,Regno8),
     J(u32),
     Beqz(Regno8,u32),
     Bnez(Regno8,u32),
     SllI(Regno,u32),
     Jr(Regno),
     Ebreak,
     Jalr(Regno),
     Add(Regno,Regno),
     Mv(Regno,Regno),
     Ldwsp(Regno,u32),
     Swsp(u32,Regno),
     None
}

#[derive(Debug)]
enum RiscvOpImac {
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
  Amo(AmoOp,Regno,Regno,Regno,bool,bool),
  C(RiscvOpC),
  None
}
  
#[bitmatch]
fn decode(inst: u32) -> RiscvOpImac {
    use RiscvOpImac::*;
    type C = RiscvOpC;
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
        "fffffql bbbbb aaaaa 010 ddddd 01011 11" => Amo(f.into(),d.into(),a.into(),b.into(),q==1,l==1),

	"000 i iiiii ii ddd 00"  => C(C::Add4spn(d.into(),imm!(i;nzuimm[5:4 9:6 2:2 3:3]))),
	"010 i iiaaa ii ddd 00"  => C(C::Ldw(d.into(),imm!(i;uimm[5:3 2:2 6:6]))),
	"000 0 00000 00 000 01"  => C(C::Nop),
	"000 i ddddd ii iii 01"  => C(C::Addi(d.into(),imm!(i;nzimm[5:5 4:0]))),
	"001 i iiiii ii iii 01"  => C(C::Jal(imm!(i;sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5]))),
	"001 i ddddd ii iii 01"  => C(C::Addiw(d.into(),imm!(i; sx[5:5 4:0]))),
	"010 i ddddd ii iii 01"  => C(C::Li(d.into(),imm!(i; nzimm[4:4 6:6 8:7 5:5]))),
	"011 i 00010 ii iii 01"  => C(C::Addi16sp(imm!(i;nzimm[4:4 6:6 8:7 5:5]))),
	"011 i ddddd ii iii 01"  => C(C::Li(d.into(),imm!(i; upper nzimm[4:4 6:6 8:7 5:5]))),
	"100 i 00ddd ii iii 01"  => C(C::SrlI(d.into(),imm!(i;nzimm[16:12]))),
	"100 i 01ddd ii iii 01"  => C(C::SrlaI(d.into(),imm!(i;nzimm[16:12]))),
	"100 i 10ddd ii iii 01"  => C(C::AndI(d.into(),imm!(i;nzimm[16:12]))),
	"100 0 11ddd 00 bbb 01"  => C(C::Sub(d.into(),b.into())),
	"100 0 11ddd 01 bbb 01"  => C(C::Xor(d.into(),b.into())),
	"100 0 11ddd 10 bbb 01"  => C(C::Ior(d.into(),b.into())),
	"100 0 11ddd 11 bbb 01"  => C(C::And(d.into(),b.into())),
        "101 i iiiii ii iii 01"  => C(C::J(imm!(i; sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5]))),
	"110 i iiaaa ii iii 01"  => C(C::Beqz(a.into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5]))),
	"110 i iiaaa ii iii 01"  => C(C::Bnez(a.into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5]))),
	"000 i ddddd ii iii 10"  => C(C::SllI(d.into(),imm!(i; nzuimm[5:5 4:0]))),
	"100 0 aaaaa 00 000 10"  => C(C::Jr(a.into())),
	"100 1 00000 00 000 10"  => C(C::Ebreak),
	"100 1 aaaaa 00 000 10"  => C(C::Jalr(a.into())),
	"100 1 ddddd aa aaa 10"  => C(C::Add(d.into(),a.into())),
	"100 0 ddddd aa aaa 10"  => C(C::Mv(d.into(),a.into())),
	"010 i ddddd ii iii 10"  => C(C::Ldwsp(d.into(),imm!(i; uimm[5:5 4:2 7:6]))),
	"110 i iiiii aa aaa 10"  => C(C::Swsp(imm!(i; uimm[5:2 7:6]),a.into())),


         _ => RiscvOpImac::None
    }
}


#[test]
fn t0 () {
    assert_eq!("Mul(Divu, X8, X8, X18)",format!("{:?}",decode(0x03245433)));
}

fn strip(s : String) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }
macro_rules! check { 
  ( $($opc:literal => $note:literal );* ) => {
     $(
        {
	 let res   = decode($opc);
	 let sres : String = strip(format!("{:?}",res));
	 let mut n = $note.split("//");
	 match n.next() {
	   Some(t) =>
              println!("{:8} {:30} => {}",sres==strip(t.to_string()),sres, t),
	   None => {}
	 }
	}
      );*
  }
}


fn main() {
   check! {
     0x80000537 => "Lui(2147483648)" ;
     0xfe079ce3 => "Branch(Bne, X15, X0, 8184)" ;
     0xff872683 => "Load(Lw, X13, X14, 4088)" ;
     0x00f72023 => "Store(Sw, X0, X14, 15)" ;
     0x01010113 => "AluI(AddI, X2, X2, 16)" ;
     0x40d90933 => "Alu(Sub, X18, X18, X13)" ;
     0x13641073 => "Csr(Csrrw, X0, X8, 155)" ;
     0x03245433 => "Mul(Divu, X8, X8, X18)";
     0x12450513 => "AluI(AddI, X10, X10, 292)";
     0x12048513 => "AluI(AddI,X10,X9,288) //80000046:	12048513          	addi	a0,s1,288 # 80000120 <_sstack+0xffffdf40>";
     0x0001     => "C(Nop)";
     0x004C     => "C(Add4spn(X3, 4))";
     0x3fc9     => "C(Jal(4050))     // 80000060:	3fc9                	jal	80000032 <lprint>";
     0x3779     => "C(Jal(...))      // 80000082:	3779                	jal	80000010 <asm_demo_func>";
     0x1141     => "C(Addi(X2,-16))  //	80000010:	1141                	addi	sp,sp,-16"
   }
}
