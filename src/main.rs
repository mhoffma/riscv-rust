#![allow(unused,non_snake_case)]
//#[cfg(not(test))] 
//use log::{info, warn}; // Use log crate when building application
 
//#[cfg(test)]
//use std::{println as info, println as warn}; // Workaround to use prinltn! for logs.
use clap::Parser;
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
      Undef
    }
    impl From<u32> for $ty {
        fn from(x: u32) -> $ty {
           use $ty::*;
           match x {
              $($val => $enum,)*
              _ => Undef
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
        let o = if $sx && v!=0 { v | _m}
                else { v };

        if $dbg {
          println!("v={:08x} _m={:08x} o={:08x} {}:{} sz={} p={}",v,_m,o,$m,$l,sz,p)
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
   assert_eq!(fimm!(0x80000537; [31:12]),5468160);
}

fenum!{Regno = { X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,
                 X16,X17,X18,X19,X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31 } }

impl Into<usize> for Regno {
    fn into(self) -> usize {
        self as usize
    }
}

fenum!{Regabi = { Zero, Ra, Sp, Gp, Tp, T0, T1, T2,
        Fp, S1, A0, A1, A2, A3, A4, A5,
        A6, A7, S2, S3, S4, S5, S6, S7,
        S8, S9, S10, S11, T3, T4, T5, T6 } }

fenum!{ BranchOp = { Beq:0, Bne:1,Blt:4,Bgt:5,Bltu:6,Bgeu:7 } }

fenum!{ LoadOp = { Lb, Lh, Lw, Lbu, Lhu } }

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
   Csrrw:1,Csrrs:2,Csrrc:3,
   Csrrwi:5,Csrrsi:6,Csrrci:7
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
  // sz --- args
  Lui(u8,Regno,u32),
  Auipc(u8,Regno,u32),
  Jal(u8,Regno,u32),
  Jalr(u8,Regno,Regno,u32),
  Fencei(u8),
  Branch(u8,BranchOp,Regno,Regno,u32),
  Load(u8,LoadOp,Regno,Regno,u32),
  Store(u8,StoreOp,Regno,Regno,u32),
  AluI(u8,AluOp,Regno,Regno,u32),
  Alu(u8,AluOp,Regno,Regno,Regno),
  Csr(u8,CsrOp,Regno,Regno,u32),
  Sys(u8,u32),  
  Mult(u8,MulOp,Regno,Regno,Regno),
  Amo(u8,AmoOp,Regno,Regno,Regno,bool,bool),
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
          "uuuuuuu uuuuu uuuuu uuu ddddd 01101 11" => Lui(4,d.into(),   imm!(u; [31:12])),
          "uuuuuuu uuuuu uuuuu uuu ddddd 00101 11" => Auipc(4,d.into(), imm!(u; [31:12])),
          "uuuuuuu uuuuu uuuuu uuu ddddd 11011 11" => Jal(4,d.into(),   imm!(u; [20:20 10:1 11:11 19:12])),
          "iiiiiii iiiii aaaaa 000 ddddd 11001 11" => Jalr(4,d.into(),a.into(),imm!(i;[11:0])),
          "uuuuuuu uuuuu uuuuu uuu ddddd 00011 11" => Fencei(4),
          "iiiiiii bbbbb aaaaa fff iiiii 11000 11" => Branch(4,f.into(),a.into(),b.into(),imm!(i; sx[12:12 10:5 4:1 11:11])),
          "iiiiiii iiiii aaaaa fff ddddd 00000 11" => Load(4,f.into(),d.into(),a.into(),  imm!(i;[11:0])),
          "iiiiiii bbbbb aaaaa fff iiiii 01000 11" => Store(4,f.into(),a.into(),b.into(), imm!(i;[11:5 4:0])),
          "ifiiiii iiiii aaaaa fff ddddd 00100 11" => AluI(4,f.into(),d.into(),a.into(),  imm!(i;[11:0])),
          "iiiiiii iiiii 00000 000 00000 11100 11" => Sys(4,                              imm!(i;[11:0])),
          "iiiiiii iiiii aaaaa fff ddddd 11100 11" => Csr(4,f.into(),d.into(),a.into(),   imm!(i;[11:0])),
          "0f00000 bbbbb aaaaa fff ddddd ooooo 11" => Alu(4,f.into(),d.into(),a.into(),b.into()),
          "0000001 bbbbb aaaaa fff ddddd ooooo 11" => Mult(4,f.into(),d.into(),a.into(),b.into()),
          "fffffql bbbbb aaaaa 010 ddddd 01011 11" => Amo(4,f.into(),d.into(),a.into(),b.into(),q==1,l==1),

          "000 i iiiii ii ddd 00"  => AluI(2,Add,(d+8).into(),X2,imm!(i;nzuimm[5:4 9:6 2:2 3:3])),   //   Add4spn(Regno,u32),
          "010 i iiaaa ii ddd 00"  => Load(2,Lw,(d+8).into(),(a+8).into(),imm!(i;uimm[5:3 2:2 6:6])),//   Ldw(Regno8,u32),
          "000 0 00000 00 000 01"  => AluI(2,Add,X0,X0,0),                                           //   Addi(Regno,u32),
          "000 i ddddd ii iii 01"  => AluI(2,Add,d.into(),d.into(),imm!(i;nzimm[5:5 4:0])),          //   Nop,
          "001 i iiiii ii iii 01"  => Jal(2,X1,imm!(i;sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5])),     //   Jal(u32),
          "001 i ddddd ii iii 01"  => AluI(2,Add,d.into(),d.into(),imm!(i; sx[5:5 4:0])),            //   Addiw(Regno,u32),
          "010 i ddddd ii iii 01"  => Lui(2,d.into(),imm!(i; nzimm[4:4 6:6 8:7 5:5])),               //   Li(Regno,u32),
          "011 i 00010 ii iii 01"  => AluI(2,Add,X2,X2,imm!(i;nzimm[4:4 6:6 8:7 5:5])),              //   Addi16sp(u32),
          "011 i ddddd ii iii 01"  => Lui(2,d.into(),imm!(i; upper nzimm[4:4 6:6 8:7 5:5])),         //
          "100 i 00ddd ii iii 01"  => AluI(2,Srl,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),    //   SrlI(Regno8,u32),
          "100 i 01ddd ii iii 01"  => AluI(2,Sra,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),    //   SrlaI(Regno8,u32),
          "100 i 10ddd ii iii 01"  => AluI(2,And,(d+8).into(),(d+8).into(),imm!(i;nzimm[16:12])),    //   AndI(Regno8,u32),
          "100 0 11ddd 00 bbb 01"  => Alu(2,Sub,(d+8).into(),(d+8).into(),b.into()),                 //   Sub(Regno8,Regno8),
          "100 0 11ddd 01 bbb 01"  => Alu(2,Xor,(d+8).into(),(d+8).into(),b.into()),                 //   Xor(Regno8,Regno8),
          "100 0 11ddd 10 bbb 01"  => Alu(2,Ior,(d+8).into(),(d+8).into(),b.into()),                 //   Ior(Regno8,Regno8),
          "100 0 11ddd 11 bbb 01"  => Alu(2,And,(d+8).into(),(d+8).into(),b.into()),                 //   And(Regno8,Regno8),
          "101 i iiiii ii iii 01"  => Jal(2,X0,imm!(i; sx[11:11 4:4 9:8 10:10 6:6 7:7 3:1 5:5])),    //   J(u32),
          "110 i iiaaa ii iii 01"  => Branch(2,Beq,X0,(a+8).into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5])),//   Beqz(Regno8,u32),
          "110 i iiaaa ii iii 01"  => Branch(2,Bne,X0,(a+8).into(),imm!(i; sx[8:8 4:3 7:6 2:1 5:5])),//   Bnez(Regno8,u32),
          "000 i ddddd ii iii 10"  => AluI(2,Sll,d.into(),d.into(),imm!(i; nzuimm[5:5 4:0])),        //   SllI(Regno,u32),
          "100 1 00000 00 000 10"  => Sys(2,1),                                                      //   Ebreak,
          "100 0 00001 00 000 10"  => Jalr(2,X0,X1,0),                                               //   ret???? Jalr(Regno),    
          "100 1 aaaaa 00 000 10"  => Jalr(2,X0,a.into(),0),                                         //   Jalr(Regno),
          "100 1 ddddd aa aaa 10"  => Alu(2,Add,d.into(),d.into(),a.into()),                         //   Add(Regno,Regno),
          "100 0 ddddd aa aaa 10"  => Alu(2,Add,d.into(),a.into(),X0),                               //   Mv(Regno,Regno),
          "010 i ddddd ii iii 10"  => Load(2,Lw,d.into(),X2,imm!(i; uimm[5:5 4:2 7:6])),             //   Ldwsp(Regno,u32),
          "110 i iiiii aa aaa 10"  => Store(2,Sw,X2,a.into(),imm!(i; uimm[5:2 7:6])),                //   Swsp(Regno,u32),

           _ => RiscvOpImac::None
      }
  }
}

#[test]
fn t0 () {
    assert_eq!("Mult(Divu, X8, X8, X18)",format!("{:?}",RiscvOpImac::decode(0x03245433)));
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
  fn readcsr(self, csrno: u32) -> u32 {
    match csrno {
      0x340 => self.mscratch,
      0x305 => self.mtvec,
      0x304 => self.mie,
      0xC00 => self.get_cycle(),
      0x344 => self.mip,
      0x341 => self.mepc,
      0x300 => self.mstatus,
      0x342 => self.mcause,
      0x343 => self.mtval,
      0xf11 => 0xff0ff0ff, //mvendorid
      0x301 => 0x40401101, //misa (XLEN=32, IMA+X)
      _ => self.external_readcsr(csrno)
    }
  }
  
  fn writecsr(&mut self, csrno: u32, val: u32) {
    match csrno {
      0x340 => self.mscratch = val,
      0x305 => self.mtvec = val,
      0x304 => self.mie = val,
      0x344 => self.mip = val,
      0x341 => self.mepc = val,
      0x300 => self.mstatus = val,
      0x342 => self.mcause = val,
      0x343 => self.mtval = val,
      _ => self.external_writecsr(csrno,val)
    }
  }
  // need to make these call functions either lambdas or via inherit
  fn get_cycle(self) -> u32 { 0 }  
  fn external_readcsr(self,csrno:u32) -> u32 { 0 }
  fn external_writecsr(self,csrno:u32,val:u32) {
     println!("external_writecsr({} : {:08x})",csrno,val)
  }

  fn print(self) {
     for i in 0..31 {
        println!("{:?} {:08x} {:?}",Regno::from(i), self.regs[i as usize],Regabi::from(i))
     }
  }
}

struct Sim {
   arch : ArchState,
   base : u32,
   alignment_mask : u32,
   mem  : Vec<u8>
}

#[derive(Debug)]
enum TrapKind {
  PCalignmentFault = 0,
  LoadInstructionFault = 1,
  IllegalInstruction = 2,
  Breakpoint = 3,
  LoadDataFault = 5,
  AMOmissalignedFault = 6,
  StoreAMOFault = 7,
  EnvCallU = 8,
  EnvCallM = 11,
  InstructionPageFault = 12,
  LoadPageFault = 13,
  StoreAMOPageFault = 15,
  TimerInterrupt = 0x80000007,
  None
}
#[derive(Debug)]
enum ReadResult {
  // isz,op, dst, rs1a, rs1, rs2a, rs2
  AluOperands(u8,AluOp,Regno,Regno,u32,Regno,u32),
  MulOperands(u8,MulOp,Regno,Regno,u32,Regno,u32),
  CsrOperands(u8,CsrOp,Regno,Regno,u32,u32,u32),  
  LoadOperands(u8,LoadOp,Regno,Regno,u32,u32),
  StoreOperands(u8,StoreOp,Regno,u32,Regno,u32,u32),
  BranchOperands(u8,BranchOp,Regno,u32,Regno,u32,u32,u32),  // rs1a,rs1,rs2a,rs2,imm,pc
  JumpOperands(u8,Regno,u32,u32), // dst,imm,pc
  JalrOperands(u8,Regno,Regno,u32,u32,u32), // dst,rs1,rs1v,imm,pc
  SysOperands(u8,u32),
  AmoOperands(u8,AmoOp,Regno,Regno,u32,Regno,u32),
  None
}
enum ExecuteResult {
  OkNoop(u8),
  OkBr(u8,Regno,u32,bool,u32),
  OkWb(u8,Regno,u32),
  OkCsr(u8,Regno,u32,u32,u32), //isz,dst,csrval,csrno, csrval)
  Wfi(u8),
  Trap(TrapKind)
}


enum WriteBackResult {
  OK(u32),
  OkBr(u32,bool,u32),
  Wfi(u32),  
  Trap(TrapKind)
}


impl Sim {
     fn translate_addr(&self,ea : u32, amask : u32, afault: TrapKind, lfault: TrapKind)
     -> Result<usize,TrapKind> {
       let sz = self.mem.len();
       if ea&amask != 0 {
          Err(afault)
       } else if ea < self.base {
          Err(lfault) 
       } else {
          let a = u32::wrapping_sub(ea, self.base);
          if a > self.base {
             Err(lfault)
          } else {
             Ok(a as usize)
          }
       }
     }
     fn external_load_data(&self, ea :u32) -> u32 {0}
     fn external_store_data(&mut self, ea :u32, value: u32) {}     
     
     fn load_instruction(&self, ea: u32) -> Result<u32,TrapKind> {
       use TrapKind::*;
       self.translate_addr(ea,self.alignment_mask,PCalignmentFault,LoadInstructionFault).and_then(|a|  {
                 let input = &self.mem[a..a+4];
                 Ok(u32::from_le_bytes(input.try_into().unwrap())) })
     }
     
     fn load_data(&self, ea :u32, sz : u32, signed : bool) -> Result<u32,TrapKind> {
       use TrapKind::*;     
       if ea >= 0x10000000 && ea < 0x12000000 {
           Ok(self.external_load_data(ea))
       } else {
       self.translate_addr(ea,sz-1,LoadDataFault,LoadDataFault).and_then(|a| {
           match sz {
             1 => {
                    let input = &self.mem[a..a+1];
                    Ok(if signed { ((input[0] as i8) as i32) as u32 }
                       else      { input[0] as u32 })
                  },
             2 => {
                    let input = &self.mem[a..a+2];       
                    Ok(if signed { (i16::from_le_bytes(input.try_into().unwrap()) as i32) as u32 }
                       else      { i16::from_le_bytes(input.try_into().unwrap()) as u32 })
                  },
             4 => {
                    let input = &self.mem[a..a+4];
                    Ok(u32::from_le_bytes(input.try_into().unwrap()))
                  },
             _ => Err(LoadDataFault)
           } })}
     }
     fn store_data(&mut self, ea :u32, sz : u32, value: u32) -> Result<(),TrapKind> {
       use TrapKind::*;
       if ea >= 0x10000000 && ea < 0x12000000 {
           self.external_store_data(ea,value);          
           Ok(())       
       } else {
       self.translate_addr(ea,sz-1,AMOmissalignedFault,StoreAMOPageFault).and_then(|a| {
           let v = u32::to_le_bytes(value);
	         self.mem[a..a+v.len()].copy_from_slice(&v);
           Ok(())
       })}
     }

     fn decode(&self, ir : u32) -> RiscvOpImac {
        RiscvOpImac::decode(ir)
     }

     fn readoperands(&self,  opcode : RiscvOpImac, pc : u32) -> ReadResult {
       use RiscvOpImac::*;
       use ReadResult::*;
       match opcode {
         Lui(isz,dst,imm) =>
           AluOperands(isz,AluOp::Add,dst,Regno::X0, imm, Regno::X0, 0),
         Auipc(isz,dst,imm) =>
           AluOperands(isz,AluOp::Add,dst,Regno::X0,pc,Regno::X0,imm),   
         Alu(isz,op,dst,rs1,rs2) => 
           AluOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],rs2,self.arch.regs[rs2 as usize]),
         AluI(isz,op,dst,rs1,imm) => 
           AluOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],Regno::X0,imm),
         Csr(isz,op,dst,rs1,csrno) => 
           CsrOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],csrno,self.arch.readcsr(csrno)),
         Sys(isz,csrno) =>
           SysOperands(isz,csrno),
         Mult(isz,op,dst,rs1,rs2) => 
           MulOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],rs2,self.arch.regs[rs2 as usize]),
         Load(isz,op,dst,rs1,imm) =>
           LoadOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],imm),        
         Store(isz,op,rs1,src,imm) =>
           StoreOperands(isz,op,rs1,self.arch.regs[rs1 as usize],src,self.arch.regs[src as usize],imm),
         Branch(isz,op,rs1,rs2,imm) =>
           BranchOperands(isz,op,rs1,self.arch.regs[rs1 as usize],rs2,self.arch.regs[rs2 as usize],imm,pc),
         Jal(isz,dst,imm) =>
           JumpOperands(isz,dst,imm,pc),
         Jalr(isz,dst,rs1,imm) =>
           JalrOperands(isz,dst,rs1,self.arch.regs[rs1 as usize],imm,pc),
         Amo(isz,op,dst,rs1,rs2,q,l) =>
           AmoOperands(isz,op,dst,rs1,self.arch.regs[rs1 as usize],rs2,self.arch.regs[rs2 as usize]),
         _ => ReadResult::None
       }
     }

     fn execute(&mut self, rv : ReadResult) -> ExecuteResult {
       use Regno::*;
       use AluOp::*;
       use MulOp::*;       
       use LoadOp::*;
       use StoreOp::*;
       use BranchOp::*;
       use CsrOp::*;
       use AmoOp::*;           
       use RiscvOpImac::*;
       use ReadResult::*;
       use ExecuteResult::*;
       use TrapKind::*;

       match rv {
         AluOperands(isz,op,dst,rs1a,rs1,rs2a,rs2) =>
            match op {
                  Add  => OkWb(isz,dst,rs1 + rs2),
                  Sll  => OkWb(isz,dst,rs1 << (rs2&0x1f)),
                  Slt  => OkWb(isz,dst,((rs1 as i32) < (rs2 as i32)) as u32),
                  Sltu => OkWb(isz,dst,(rs1 < rs2) as u32),
                  Xor  => OkWb(isz,dst,rs1 ^ rs2),
                  Srl  => OkWb(isz,dst,rs1 >> (rs2 & 0x1F)),
                  Ior  => OkWb(isz,dst,rs1 | rs2),
                  And  => OkWb(isz,dst,rs1 & rs2),
                  Sub  => OkWb(isz,dst,rs1 - rs2),
                  Sra  => OkWb(isz,dst,((rs1 as i32) - (rs2 as i32)) as u32),
                  _ => Trap(IllegalInstruction)
            },
         MulOperands(isz,op,dst,rs1a,rs1,rs2a,rs2) =>
            match op {
                  Mul  => OkWb(isz,dst,rs1 * rs2),
                  Mulh  => OkWb(isz,dst,{
                     let a = i64::from(rs1 as i32);
                     let b = i64::from(rs2 as i32);
                     let r = (a * b)>>32;
                     r as u32
                  }),
                  Mulsu  => OkWb(isz,dst,{
                     let a = i64::from(rs1 as i32);
                     let b = i64::from(rs2);
                     let r = (a * b)>>32;
                     r as u32
                  }),
                  Mulhu  => OkWb(isz,dst,{
                     let a = i64::from(rs1);
                     let b = i64::from(rs2);
                     let r = (a * b)>>32;
                     r as u32
                  }),
                  Div  => OkWb(isz,dst,{
                     if rs2 == 0 { 0xFFFF_FFFF  }
                     else if rs1 == 0x8000_0000 && rs2 == 0xFFFF_FFFF { rs1 }
                     else {
                        ((rs1 as i32)/(rs2 as i32)) as u32
                     }}),
                  Divu =>  OkWb(isz,dst,{
                     if rs2 == 0 { 0xFFFF_FFFF  }
                     else { rs1 / rs2 }}),
                  Rem  => OkWb(isz,dst,{
                     if rs2 == 0 { rs1  }
                     else if rs1 == 0x8000_0000 && rs2 == 0xFFFF_FFFF { rs1 }
                     else {
                        ((rs1 as i32)%(rs2 as i32)) as u32
                     }}),
                  Remu =>  OkWb(isz,dst,{
                     if rs2 == 0 { rs1  }
                     else { rs1 % rs2 }}),
                  _ => Trap(IllegalInstruction)              
           },
         LoadOperands(isz,op,dst,rs1a,rs1,imm) =>
           match op {
                 Lb  => match self.load_data(rs1+imm,1,true) {
                           Ok(res) => OkWb(isz,dst,res),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Lbu  => match self.load_data(rs1+imm,1,false) {
                           Ok(res) => OkWb(isz,dst,res),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Lh  => match self.load_data(rs1+imm,2,true) {
                           Ok(res) => OkWb(isz,dst,res),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Lhu  => match self.load_data(rs1+imm,2,false) {
                           Ok(res) => OkWb(isz,dst,res),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Lw  => match self.load_data(rs1+imm,4,false) {
                           Ok(res) => OkWb(isz,dst,res),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 _ => Trap(IllegalInstruction)
           },
         StoreOperands(isz,op,rs1a,rs1,srca,src,imm) =>
           match op {
                 Sb  => match self.store_data(rs1+imm,1,src) {
                           Ok(res) => OkWb(isz,X0,0),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Sh  => match self.store_data(rs1+imm,2,src) {
                           Ok(res) => OkWb(isz,X0,0),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 Sw  => match self.store_data(rs1+imm,4,src) {
                           Ok(res) => OkWb(isz,X0,0),
                           Err(t)  => ExecuteResult::Trap(t)
                 },
                 _ => Trap(IllegalInstruction)           
           },    
         BranchOperands(isz,op,rs1a,rs1,rs2a,rs2,imm,pc) =>
           match op {
                 Beq => OkBr(isz,X0,0,rs1 == rs2, pc + imm),
                 Bne => OkBr(isz,X0,0,rs1 != rs2, pc + imm),
                 Blt => OkBr(isz,X0,0,(rs1 as i32) < (rs2 as i32), pc + imm),
                 Bgt => OkBr(isz,X0,0,(rs1 as i32) > (rs2 as i32), pc + imm),
                 Bltu => OkBr(isz,X0,0,rs1 < rs2, pc + imm),
                 Bgeu => OkBr(isz,X0,0,rs1 > rs2, pc + imm),
                 _ => Trap(IllegalInstruction)           
           },
           
        JumpOperands(isz,dst,raddr,pc) =>
           OkBr(isz,dst,pc+(isz as u32),true,pc.overflowing_add(raddr).0),
           
        JalrOperands(isz,dst,rs1a,rs1,raddr,pc) => {
           let nextpc = rs1+raddr;
           if (nextpc & self.alignment_mask) == 0 { OkBr(isz,dst,pc+(isz as u32),true,nextpc) }
           else                                   { Trap(IllegalInstruction) }
        },
        CsrOperands(isz,op,dst,rs1a,rs1,csrno,csrval) => 
           match op {
              Csrrw  => OkCsr(isz,dst,csrval,csrno, rs1),
              Csrrs  => OkCsr(isz,dst,csrval,csrno, csrval | rs1),
              Csrrc  => OkCsr(isz,dst,csrval,csrno, csrval & !rs1),
              Csrrwi => OkCsr(isz,dst,csrval,csrno, rs1a as u32),
              Csrrsi => OkCsr(isz,dst,csrval,csrno, csrval | rs1a as u32),
              Csrrci => OkCsr(isz,dst,csrval,csrno, csrval & !(rs1a as u32)),
              _ => Trap(IllegalInstruction)
        },
        SysOperands(isz,csrno) => {
           match csrno {
             0x105 => { //self.arch.wfi()
                        self.arch.mstatus    = self.arch.mstatus | 8;
                        self.arch.extraflags = self.arch.extraflags | 4;
                        Wfi(isz)
             },
             2     => { // self.arch.mret()
                        //https://raw.githubusercontent.com/riscv/virtual-memory/main/specs/663-Svpbmt.pdf
                        //Table 7.6. MRET then in mstatus/mstatush sets MPV=0, MPP=0, MIE=MPIE, and MPIE=1. La
                        // Should also update mstatus to reflect correct mode.
                        let mstatus    = self.arch.mstatus;
                        let extraflags = self.arch.extraflags;
                        self.arch.mstatus = (( mstatus & 0x80) >> 4) | ((extraflags&3) << 11) | 0x80;
                        self.arch.extraflags = (extraflags & !3) | ((mstatus >> 11) & 3) ;
                        OkBr(isz,X0,0,true,self.arch.mepc)
             },
             0     => Trap(if (self.arch.extraflags&3)!=0 { EnvCallM } else { EnvCallU }),
             1     => Trap(Breakpoint),
             _     => OkNoop(isz)
           }
        },
        AmoOperands(isz,op,dst,rs1a,rs1,rs2a,rs2) => {
          match self.load_data(rs1,4,false) {
            Ok(mut rval) => {      
                  let mut dowrite = true;
                  let mut output  = rs2;
                  let mut illegal = false;
                  match op {
                     Lrw => { self.arch.extraflags = (self.arch.extraflags & 7) | (rs1<<3); dowrite=false;  }
                     Scw => { rval = ((self.arch.extraflags >> 3) != (rs1 & 0x1fff_ffff)) as u32;    dowrite=rval==0; } // reservation slot
                     Amoswapw  => { },
                     Amoaddw   => { output = rs2 + rval; },
                     Amoxorw   => { output = rs2 ^ rval; },
                     Amoandw   => { output = rs2 & rval; },
                     Amoorw    => { output = rs2 | rval; },
                     Amominw   => { output = if (rs2 as i32) < (rval as i32) { rs2 } else { rval } },
                     Amomaxw   => { output = if (rs2 as i32) > (rval as i32) { rs2 } else { rval } },
                     Amominuw  => { output = if rs2 < rval { rs2 } else { rval } },
                     Amomaxuw  => { output = if rs2 > rval { rs2 } else { rval } },
                     _         => { illegal = true }
                  }
                  if illegal { Trap(IllegalInstruction) }
                  else if dowrite {
                     match self.store_data(rs1,4,output) {
                         Ok(res) => OkWb(isz,dst,rval),
                         Err(t)  => ExecuteResult::Trap(t)
                     }
                  } else { OkWb(isz,dst,rval) }
               },
            Err(t) => Trap(t)
          }
        },
         _ => Trap(IllegalInstruction)
        }
   }

   fn writeback(&mut self, wb : ExecuteResult) -> WriteBackResult {
     use ExecuteResult::*;
     match wb {
       OkWb(isz,dst,rval) => {
           self.arch.regs[dst as usize] = rval;
           WriteBackResult::OK(isz as u32)
       },
       OkBr(isz,dst,rval,taken,nextpc) => {
           self.arch.regs[dst as usize] = rval;
           WriteBackResult::OkBr(isz as u32,taken,nextpc)
       },
       OkCsr(isz,dst,rval,csrno, csrval) => {
           self.arch.regs[dst as usize] = rval;
           self.arch.writecsr(csrno,csrval);
           WriteBackResult::OK(isz as u32)
       },
       OkNoop(isz) => WriteBackResult::OK(isz as u32),
       Wfi(isz)    => WriteBackResult::OK(isz as u32),
       ExecuteResult::Trap(t) => WriteBackResult::Trap(t)
     }
   }


   fn functional_step (&mut self,trace:bool) -> Result<u32,TrapKind> {
      use WriteBackResult::*;
      let pc = self.arch.pc;
      let ir = self.load_instruction(pc).unwrap();

      let dstage  = self.decode(ir);
      if trace { println!("{:08x}: {:08x} {:?}",pc,ir,dstage); }
      let rstage  = self.readoperands(dstage, pc);
      if trace { println!("{:08x}: {:08x} {:?}",pc,ir,rstage); }     
      let estage  = self.execute(rstage);
      let mut branch = false;
      let mut trap   : TrapKind  = TrapKind::None;
      let mut sz     : u32 = 0;
      let mut nextpc : u32 = 0;

      match self.writeback(estage) {
         OK(isz)                 => { sz=isz },
         Wfi(isz)                => { sz=isz },
         OkBr(isz,taken,newaddr) => { sz=isz; branch=taken; nextpc=newaddr },
         Trap(kind) => {
            return Err(kind);
         },
      };
      self.arch.pc = if branch { nextpc } else { pc + sz };
      Ok(0)
   }
}


fn strip(s : String) -> String { s.chars().filter(|c| !c.is_whitespace()).collect() }
macro_rules! check {
   ( $test:expr ; $($opc:literal => $note:literal );* ) => {
     $(
        {
         let res   = RiscvOpImac::decode($opc);
         let sres : String = strip(format!("{:?}",res));
         let mut n = $note.split("//");
         match n.next() {
           Some(t) =>
              if $test { assert_eq!(sres,strip(t.to_string())) }
              else { println!("{:8} {:30} => {}",sres==strip(t.to_string()),sres, $note) },
           None => {}
         }
        }
      );*
  }
}

#[test]
fn f1() {
   let c = cfg!(test);
   assert_eq!(c,true);
   check! { c ;
     0x80000537 => "Lui(4,X10,2147483648)" ;
     0x0091_2223 => "Store(4,Sw,X2,X9,4) // 000003e:	00912223          	sw	s1,4(sp);";
     0xfe079ce3 => "Branch(4,Bne, X15, X0, 4294967288)" ;
     0xff872683 => "Load(4,Lw, X13, X14, 4088)" ;
     0x00f72023 => "Store(4,Sw, X0, X14, 15)" ;
     0x01010113 => "AluI(4,Add, X2, X2, 16)" ;
     0x40d90933 => "Alu(4,Sub, X18, X18, X13)" ;
     0x13641073 => "Csr(4,Csrrw, X0, X8, 310)" ;
     0x03245433 => "Mult(4,Divu, X8, X8, X18)";
     0x12450513 => "AluI(4,Add, X10, X10, 292)";
     0x12048513 => "AluI(4,Add,X10,X9,288) //80000046:  12048513                addi    a0,s1,288 # 80000120 <_sstack+0xffffdf40>";
     0x0001     => "AluI(2,Add,X0,X0,0)";
     0x004C     => "AluI(2,Add,X11,X2,4)";

     0x00002117 => "Auipc(4,X2,8192)       // 80000000: 00002117                auipc   sp,0x2";
     0x1e010113 => "AluI(4,Add,X2,X2,480)  // 80000004: 1e010113                addi    sp,sp,480 # 800021e0 <_sstack>";
     0x1141     => "AluI(2,Add,X2,X2,48)   // 80000008: 1141                    addi    sp,sp,-16";
     0xc606     => "Store(2,Sw,X1,X2,12)   // 8000000a: c606                    sw      ra,12(sp)";
     0x02e000ef => "Jal(4,X1,46)           // 8000000c: 02e000ef                jal     ra,8000003a <main>";
     0x3fc9     => "Jal(2,X1,46)           // 80000060: 3fc9                    jal     80000032 <lprint>";
     0x3779     => "Jal(2,X1,-120)         // 80000082: 3779                    jal     80000010 <asm_demo_func>";
     0x1141     => "AluI(2,Add,X2,X2,-16)  // 80000010: 1141                    addi    sp,sp,-16";
     0xc616     => "Store(2,Sw,X5,X2,12)   // 80000012: c616                    sw      t0,12(sp)";
     0x00000297 => "Auipc(4,X5,0)          // 80000014: 00000297                auipc   t0,0x0";
     0x1ac28293 => "AluI(4,Add,X5,X5,428)  // 80000018: 1ac28293                addi    t0,t0,428 # 800001c0 <asm_label>";
     0x13829073 => "Csr(4,Csrrw,X0,X5,312) // 8000001c: 13829073                csrw    0x138,t0";
     0x42b2     => "Load(2,Lw,X5,X2,12)    // 80000020: 42b2                    lw      t0,12(sp)";
     0x0141     => "AluI(2,Add,X2,X2,16)   // 80000022: 0141                    addi    sp,sp,16";
     0x8082     => "Jalr(2,X1,0)           // 80000024: 8082                    ret"
   }
}

#[test]
fn f2() {
     let mut s = Sim{
        arch: ArchState::reset(),
        base: 0x8000_0000,
        alignment_mask: 1,
        mem: vec![0_u8; 1024]
     };

     for i in 0..10 {
          s.mem[i*2+0]=0x41;
          s.mem[i*2+1]=0x01;
     }
     s.arch.pc=0x8000_0000;

     for i in 0..10 {
        s.functional_step(true)?;
        println!("{:?}",s.arch);
     }
     assert_eq!(s.arch.regs[2],16*10)
}

#[derive(Parser,Debug)]
struct ProgramArgs {
  #[arg(short, long, default_value_t = String::from("baremetal_c.bin"))]
  fname : String,
  #[arg(long, default_value_t = 0)]
  bp   : u32
}

fn main() {
  let args = ProgramArgs::parse();
  let mut trace = false;
     if false {
       check!{ false ; 
         0x0091_2223 => "000003e:	00912223          	sw	s1,4(sp);"
       }
       return;
     }
     let mut s = Sim{
        arch: ArchState::reset(),
        base: 0x8000_0000,
        alignment_mask: 1,
        mem: vec![0_u8; 1<<20]
     };
     let bytes = std::fs::read(args.fname).unwrap();

     s.mem[0..bytes.len()].copy_from_slice(&bytes);
     s.arch.pc=0x8000_0000;

     loop {
        if args.bp != 0 && args.bp == s.arch.pc
           { trace=true}
        match s.functional_step(true) {
          Ok(x) =>   if trace {println!("{:?}",s.arch) }
          Err(t) => {
	  	 println!("{:?}",s.arch);
		 s.arch.print();
		 println!("{:?}", t);
		 break;
          }
        }
     }
}
