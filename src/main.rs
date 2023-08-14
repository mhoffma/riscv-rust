#![allow(unused)]
use bitmatch::bitmatch;


macro_rules! fenum {
  ($ty:ident = { $( $enum:ident ),* }
  ) => {
    #[repr(u8)]
    #[derive(Debug,Copy,Clone)]
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

impl Into<usize> for Regno {
    fn into(self) -> usize {
        self as usize
    }
}

fenum!{ BranchOp = { Beq:0, Bne:1,Blt:4,Bgt:5,Bltu:6,Bgeu:7 } }

fenum!{ LoadOp = { Lb, Lh, Lw, Lbu, Lbh } }

fenum!{ StoreOp = {  Sb, Sh, Sw } }


fenum!{ AluOp = {
   Add:0,Sll:1,Slt:2,Sltu:3,
   Xor:4,Srl:5,Ior:6,And:7,
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



#[derive(Debug)]
enum RiscvOpImac {
  Lui(Regno,u32),
  Auipc(Regno,u32),
  Jal(Regno,u32),
  Jalr(Regno,u32),
  Fencei,
  Branch(BranchOp,Regno,Regno,u32),
  Load(LoadOp,Regno,Regno,u32),
  Store(StoreOp,Regno,Regno,u32),
  AluI(AluOp,Regno,Regno,u32),
  Alu(AluOp,Regno,Regno,Regno),
  Csr(CsrOp,Regno,Regno,u32),
  Mul(MulOp,Regno,Regno,Regno),
  Amo(AmoOp,Regno,Regno,Regno,bool,bool),
  None
}

impl RiscvOpImac {
  #[bitmatch]
  fn decode(inst: u32) -> RiscvOpImac {
      use RiscvOpImac::*;
      use AluOp::*;
      use Regno::*;
      use LoadOp::*;
      use StoreOp::*;    
      use BranchOp::*;
      use CsrOp::*;    
      #[bitmatch]
      match inst {
	  "uuuuuuu uuuuu uuuuu uuu ddddd 01101 11" => Lui(d.into(),   imm!(u; [31:12])),
	  "uuuuuuu uuuuu uuuuu uuu ddddd 00101 11" => Auipc(d.into(), imm!(u; [31:12])),
	  "uuuuuuu uuuuu uuuuu uuu ddddd 11011 11" => Jal(d.into(),   imm!(u; [20:20 10:1 11:11 19:12])),
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

	  "000 i iiiii ii ddd 00"  => AluI(Add,(d+8).into(),X2,imm!(i;nzuimm[5:4 9:6 2:2 3:3])),     //   Add4spn(Regno,u32),
	  "010 i iiaaa ii ddd 00"  => Load(Lw,(d+8).into(),(a+8).into(),imm!(i;uimm[5:3 2:2 6:6])),  //	  Ldw(Regno8,u32),
	  "000 0 00000 00 000 01"  => AluI(Add,X0,X0,0),					     //	  Addi(Regno,u32),
	  "000 i ddddd ii iii 01"  => AluI(Add,d.into(),d.into(),imm!(i;nzimm[5:5 4:0])),	     //   Nop,
	  "001 i iiiii ii iii 01"  => Jal(X0,imm!(i;sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5])),	     //	  Jal(u32),
	  "001 i ddddd ii iii 01"  => AluI(Add,d.into(),d.into(),imm!(i; sx[5:5 4:0])),		     //	  Addiw(Regno,u32),
	  "010 i ddddd ii iii 01"  => Lui(d.into(),imm!(i; nzimm[4:4 6:6 8:7 5:5])),		     //	  Li(Regno,u32),
	  "011 i 00010 ii iii 01"  => AluI(Add,X2,X2,imm!(i;nzimm[4:4 6:6 8:7 5:5])),                //	  Addi16sp(u32),
	  "011 i ddddd ii iii 01"  => Lui(d.into(),imm!(i; upper nzimm[4:4 6:6 8:7 5:5])),	     //
	  "100 i 00ddd ii iii 01"  => AluI(Srl,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),	     //	  SrlI(Regno8,u32),
	  "100 i 01ddd ii iii 01"  => AluI(Sra,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),	     //	  SrlaI(Regno8,u32),
	  "100 i 10ddd ii iii 01"  => AluI(And,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),	     //	  AndI(Regno8,u32),
	  "100 0 11ddd 00 bbb 01"  => Alu(Sub,(d+8).into(),(d+8).into(),b.into()),		     //	  Sub(Regno8,Regno8),
	  "100 0 11ddd 01 bbb 01"  => Alu(Xor,(d+8).into(),(d+8).into(),b.into()),		     //	  Xor(Regno8,Regno8),
	  "100 0 11ddd 10 bbb 01"  => Alu(Ior,(d+8).into(),(d+8).into(),b.into()),		     //	  Ior(Regno8,Regno8),
	  "100 0 11ddd 11 bbb 01"  => Alu(And,(d+8).into(),(d+8).into(),b.into()),		     //	  And(Regno8,Regno8),
	  "101 i iiiii ii iii 01"  => Jal(X0,imm!(i; sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5])),	     //	  J(u32),
	  "110 i iiaaa ii iii 01"  => Branch(Beq,X0,(a+8).into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5])),  //	  Beqz(Regno8,u32),
	  "110 i iiaaa ii iii 01"  => Branch(Bne,X0,(a+8).into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5])),  //	  Bnez(Regno8,u32),
	  "000 i ddddd ii iii 10"  => AluI(Sll,d.into(),d.into(),imm!(i; nzuimm[5:5 4:0])),	     //	  SllI(Regno,u32),
	  "100 1 00000 00 000 10"  => Csr(Ebreak,X0,X0,0),					     //	  Ebreak,
	  "100 1 aaaaa 00 000 10"  => Jalr(a.into(),0),					             //	  Jalr(Regno),
	  "100 1 ddddd aa aaa 10"  => Alu(Add,d.into(),d.into(),a.into()),			     //	  Add(Regno,Regno),
	  "100 0 ddddd aa aaa 10"  => Alu(Add,d.into(),a.into(),X0),				     //	  Mv(Regno,Regno),
	  "010 i ddddd ii iii 10"  => Load(Lw,d.into(),X2,imm!(i; uimm[5:5 4:2 7:6])),		     //	  Ldwsp(Regno,u32),
	  "110 i iiiii aa aaa 10"  => Store(Sw,a.into(),X2,imm!(i; uimm[5:2 7:6])),		     //	  Swsp(Regno,u32),

	   _ => RiscvOpImac::None
      }
  }
}


#[derive(Debug,Copy,Clone,Default)]
struct ArchState {
   regs : [u32; 32],
   pc : u32,
   mstatus : u32,
   cyclel : u32,
   cycleh : u32,
   timerl : u32,
   timerh : u32,
   timermatchl : u32,
   timermatchh : u32,
   mscratch : u32,
   mtvec : u32,
   mie : u32,
   mip : u32,
   mepc : u32,
   mtval : u32,
   mcause : u32,
    // Note: only a few bits are used.  (Machine = 3, User = 0)
    // Bits 0..1 = privilege.
    // Bit 2 = WFI (Wait for interrupt)
    // Bit 3+ = Load/Store reservation LSBs.
   extraflags : u32
}

struct Sim<'a> {
   arch : ArchState,
   base : u32,
   mem  : &'a Vec<u8>
}

#[derive(Debug)]
enum TrapKind {
  PCalignmentFault = 0,
  LoadInstructionFault = 1,
  IllegalOpcode = 2,
  Breakpoint = 3,
  LoadDataFault = 5,
  StoreDataFault = 7,
  TimerInterrupt = 0x80000007,
  None
}

enum ReadResult {
  // op, dst, rs1a, rs1, rs2a, rs2
  AluOperands(AluOp,Regno,Regno,u32,Regno,u32),
  None
}
enum ExecuteResult {
  Ok(Regno,u32),
  Trap(u32)
}
enum WriteBackResult {
  Ok(u32),
  Trap(u32)
}

impl ArchState {
  fn reset() -> Self {
     ArchState {
        regs : [0; 32],
	pc : 0,
        mstatus : 0,
        cyclel : 0,
        cycleh : 0,
        timerl : 0,
        timerh : 0,
        timermatchl : 0,
        timermatchh : 0,
        mscratch : 0,
        mtvec : 0,
        mie : 0,
        mip : 0,
        mepc : 0,
        mtval : 0,
        mcause : 0,
        extraflags : 0
     }
  }
}

impl Sim<'_> {
/*
     fn new(base:u32, mem: &mut Vec<u8>) -> Self {
       Self {
       	       arch: ArchState::reset(),
	       mem: mem
	    }
     }
     */
     fn load_instruction(&self, ea: u32) -> u32 {
       0
     }

     fn decode(&self, ir : u32) -> RiscvOpImac {
     	RiscvOpImac::decode(ir)
     }

     fn readoperands(&self,  opcode : RiscvOpImac) -> ReadResult {
       use RiscvOpImac::*;
       match opcode {
         Alu(op,dst,rs1,rs2) => 
	   ReadResult::AluOperands(op,dst,rs1,self.arch.regs[rs1 as usize],rs2,self.arch.regs[rs2 as usize]),
	 AluI(op,dst,rs1,imm) => 
	   ReadResult::AluOperands(op,dst,rs1,self.arch.regs[rs1 as usize],Regno::X0,imm),
       	 _ => ReadResult::None
       }
     }

     fn execute(&self, rv : ReadResult) -> ExecuteResult {
       use RiscvOpImac::*;
       match rv {
	 ReadResult::AluOperands(op,dst,rs1a,rs1,rs2a,rs2) =>
	    match op {
		  AluOp::Add  => ExecuteResult::Ok(dst,rs1 + rs2),
		  AluOp::Sll  => ExecuteResult::Ok(dst,rs1 << (rs2&0x1f)),
		  AluOp::Slt  => ExecuteResult::Ok(dst,((rs1 as i32) < (rs2 as i32)) as u32),
		  AluOp::Sltu => ExecuteResult::Ok(dst,(rs1 < rs2) as u32),
		  AluOp::Xor  => ExecuteResult::Ok(dst,rs1 ^ rs2),
		  AluOp::Srl  => ExecuteResult::Ok(dst,rs1 >> (rs2 & 0x1F)),
		  AluOp::Ior  => ExecuteResult::Ok(dst,rs1 | rs2),
		  AluOp::And  => ExecuteResult::Ok(dst,rs1 & rs2),
		  AluOp::Sub  => ExecuteResult::Ok(dst,rs1 - rs2),
		  AluOp::Sra  => ExecuteResult::Ok(dst,((rs1 as i32) - (rs2 as i32)) as u32),
		  _ => ExecuteResult::Trap(3)
	    },
	 _ => ExecuteResult::Trap(3)
       }
   }

   fn writeback(&mut self, wb : ExecuteResult) -> WriteBackResult {
     match wb {
       ExecuteResult::Ok(dst,rval) => {
       				   self.arch.regs[dst as usize] = rval;
				   WriteBackResult::Ok(4)
       },
       ExecuteResult::Trap(t) => WriteBackResult::Trap(t)
     }
   }

   fn functional_step (&mut self) {
      let pc = self.arch.pc;
      let ir = self.load_instruction(pc);
      let dstage  = self.decode(ir);
      let rstage  = self.readoperands(dstage);
      let estage  = self.execute(rstage);
      match self.writeback(estage) {
         WriteBackResult::Ok(isz) => {
	    self.arch.pc = pc + isz
	 },
	 WriteBackResult::Trap(kind) => {
	    println!("{}",kind)
	 },
      }
   }
}

#[test]
fn t0 () {
    assert_eq!("Mul(Divu, X8, X8, X18)",format!("{:?}",RiscvOpImac::decode(0x03245433)));
}

fn strip(s : String) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }
macro_rules! check {
  ( $($opc:literal => $note:literal );* ) => {
     $(
        {
	 let res   = RiscvOpImac::decode($opc);
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
     0x01010113 => "AluI(Add, X2, X2, 16)" ;
     0x40d90933 => "Alu(Sub, X18, X18, X13)" ;
     0x13641073 => "Csr(Csrrw, X0, X8, 155)" ;
     0x03245433 => "Mul(Divu, X8, X8, X18)";
     0x12450513 => "AluI(Add, X10, X10, 292)";
     0x12048513 => "AluI(Add,X10,X9,288) //80000046:	12048513          	addi	a0,s1,288 # 80000120 <_sstack+0xffffdf40>";
     0x0001     => "AluI(Add,X0,X0,0)";
     0x004C     => "AluI(Add,X11,X2,4)";

     0x00002117 => "Auipc(X2,8192)       // 80000000:	00002117          	auipc	sp,0x2";
     0x1e010113 => "AluI(Add,X2,X2,480)  // 80000004:	1e010113          	addi	sp,sp,480 # 800021e0 <_sstack>";
     0x1141     => "AluI(Add,X2,X2,48)   // 80000008:	1141                	addi	sp,sp,-16";
     0xc606     => "Store(Sw,X1,X2,12)   // 8000000a:	c606                	sw	ra,12(sp)";
     0x02e000ef => "Jal(X1,46)           // 8000000c:	02e000ef          	jal	ra,8000003a <main>";
     0x3fc9     => "Jal(X1,46)           // 80000060:	3fc9                	jal	80000032 <lprint>";
     0x3779     => "Jal(X1,...)          // 80000082:	3779                	jal	80000010 <asm_demo_func>";
     0x1141     => "AluI(Add,X2,X2,-16)  // 80000010:	1141                	addi	sp,sp,-16";
     0xc616     => "Store(Sw,X5,X2,12)   // 80000012:	c616                	sw	t0,12(sp)";
     0x00000297 => "Auipc(X5,0)          // 80000014:	00000297          	auipc	t0,0x0";
     0x1ac28293 => "AluI(Add,X5,X5,428) // 80000018:	1ac28293          	addi	t0,t0,428 # 800001c0 <asm_label>";
     0x13829073 => "Csr(Csrrw,X0,X5,312) // 8000001c:	13829073          	csrw	0x138,t0";
     0x42b2     => "Load(Lw,X5,X2,12)    // 80000020:	42b2                	lw	t0,12(sp)";
     0x0141     => "AluI(Add,X2,X2,16)   // 80000022:	0141                	addi	sp,sp,16";
     0x8082     => "Jr(X1)               // 80000024:	8082                	ret"

   }

     let mut mem = vec![0_u8; 1024];
     let mut s = Sim{ arch: ArchState::reset(), base: 0x80000000, mem: &mem };
     
     s.arch.pc=0x8000000;
     for i in 0..10 {
        s.functional_step();
	println!("{:?}",s.arch);
     }
}
