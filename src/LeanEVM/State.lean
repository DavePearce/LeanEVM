import Mathlib.Tactic.Linarith
import LeanEVM.Util

/- =============================================================== -/
/- Bytecodes -/
/- =============================================================== -/

inductive Bytecode where
-- 0s: Stop and Arithmetic Operations
| Stop
| Add
| Sub
| Mul
| Div
-- 10s: Comparison & Bitwise Logic Operations
-- 20s: SHA3
-- 30s: Environment Information
-- 40s: Block Information
-- 50s: Stack, Memory Storage and Flow Operations
| Pop
-- 60s & 70s: Push Operations
| Push(bs:Array u8)
-- 80s: Duplication Operations
| Dup(n:u4)
-- 90s: Exchange Operations
-- a0s: Logging Operations
-- f0s: System operations
| Invalid

@[simp]
def Dup_1 := Bytecode.Dup {val:=0, isLt:=(by simp_arith)}
@[simp]
def Dup_2 := Bytecode.Dup {val:=1, isLt:=(by simp_arith)}
@[simp]
def Dup_3 := Bytecode.Dup {val:=2, isLt:=(by simp_arith)}
@[simp]
def Dup_4 := Bytecode.Dup {val:=3, isLt:=(by simp_arith)}
@[simp]
def Dup_5 := Bytecode.Dup {val:=4, isLt:=(by simp_arith)}
@[simp]
def Dup_6 := Bytecode.Dup {val:=5, isLt:=(by simp_arith)}
@[simp]
def Dup_7 := Bytecode.Dup {val:=6, isLt:=(by simp_arith)}
@[simp]
def Dup_8 := Bytecode.Dup {val:=7, isLt:=(by simp_arith)}
@[simp]
def Dup_9 := Bytecode.Dup {val:=8, isLt:=(by simp_arith)}
@[simp]
def Dup_10 := Bytecode.Dup {val:=9, isLt:=(by simp_arith)}
@[simp]
def Dup_11 := Bytecode.Dup {val:=10, isLt:=(by simp_arith)}
@[simp]
def Dup_12 := Bytecode.Dup {val:=11, isLt:=(by simp_arith)}
@[simp]
def Dup_13 := Bytecode.Dup {val:=12, isLt:=(by simp_arith)}
@[simp]
def Dup_14 := Bytecode.Dup {val:=13, isLt:=(by simp_arith)}
@[simp]
def Dup_15 := Bytecode.Dup {val:=14, isLt:=(by simp_arith)}
@[simp]
def Dup_16 := Bytecode.Dup {val:=15, isLt:=(by simp_arith)}

/- =============================================================== -/
/- Code ROM -/
/- =============================================================== -/

def MAX_CODE_SIZE := 24576

def EvmCode := Array u8

-- Read a byte at a given `pc` position within a code sequence.  If the position
-- is out-of-bounds, then `0` is returned.
def EvmCode.read(st:EvmCode)(pc:Nat) : u8 :=
  if r:pc >= st.size
  then
    U8_0
  else
    st.get {val:=pc,isLt:=(by linarith)}

-- Read `n` bytes from the code sequence starting a given `pc` position.
def EvmCode.slice(st:EvmCode)(pc:Nat)(n:Nat) : Array u8 :=
  sorry

-- Decode the instruction at a given `pc` position within the code sequence.
def EvmCode.decode (st:EvmCode)(pc:Nat) : Bytecode :=
  -- Read opcode
  let opcode : u8 := st.read pc;
  -- Decode opcode
  match opcode.val with
  -- 0s: Stop and Arithmetic Operations
  | 0x00 => Bytecode.Stop
  | 0x01 => Bytecode.Add
  | 0x02 => Bytecode.Mul
  | 0x03 => Bytecode.Sub
  | 0x04 => Bytecode.Div
  -- 10s: Comparison & Bitwise Logic Operations
  -- 20s: SHA3
  -- 30s: Environment Information
  -- 40s: Block Information
  -- 50s: Stack, Memory Storage and Flow Operations
  | 0x50 => Bytecode.Pop
  -- 60s & 70s: Push Operations
  | 0x60 => Bytecode.Push (st.slice pc 1)
  | 0x61 => Bytecode.Push (st.slice pc 2)
  | 0x62 => Bytecode.Push (st.slice pc 3)
  | 0x63 => Bytecode.Push (st.slice pc 4)
  | 0x64 => Bytecode.Push (st.slice pc 5)
  | 0x65 => Bytecode.Push (st.slice pc 6)
  | 0x66 => Bytecode.Push (st.slice pc 7)
  | 0x67 => Bytecode.Push (st.slice pc 8)
  | 0x68 => Bytecode.Push (st.slice pc 9)
  | 0x69 => Bytecode.Push (st.slice pc 10)
  | 0x6a => Bytecode.Push (st.slice pc 11)
  | 0x6b => Bytecode.Push (st.slice pc 12)
  | 0x6c => Bytecode.Push (st.slice pc 13)
  | 0x6d => Bytecode.Push (st.slice pc 14)
  | 0x6e => Bytecode.Push (st.slice pc 15)
  | 0x6f => Bytecode.Push (st.slice pc 16)
  -- 80s: Duplication Operations
  | 0x80 => Dup_1
  | 0x81 => Dup_2
  | 0x82 => Dup_3
  | 0x83 => Dup_4
  | 0x84 => Dup_5
  | 0x85 => Dup_6
  | 0x86 => Dup_7
  | 0x87 => Dup_8
  | 0x88 => Dup_9
  | 0x89 => Dup_10
  | 0x8a => Dup_11
  | 0x8b => Dup_12
  | 0x8c => Dup_13
  | 0x8d => Dup_14
  | 0x8e => Dup_15
  | 0x8f => Dup_16
  -- 90s: Exchange Operations
  -- a0s: Logging Operations
  -- f0s: System operations
  | _ => Bytecode.Invalid

/- =============================================================== -/
/- Stack -/
/- =============================================================== -/
def EvmStack := List u256

-- Pop an item of the EVM stack
@[simp] def EvmStack.pop (st:EvmStack)(n:Nat)(r:n <= st.length) : EvmStack :=
  match st with
  | h::t =>
      if n == 0 then st
      else
        EvmStack.pop t (n-1) (by
        rw [Nat.sub_le_iff_le_add]
        rw [<- len_succ h t]
        exact r
  )
  | [] => []

-- Push an item onto the EVM stack
@[simp] def EvmStack.push (st:EvmStack)(n:u256) : EvmStack :=
  n::st

-- Peek an item on the EVM stack
@[simp] def EvmStack.peek (st:EvmStack)(i:Fin st.length) : u256 :=
  st.get i

/- =============================================================== -/
/- Ethereum Virtual Machine -/
/- =============================================================== -/

structure Evm where
  stack: EvmStack

@[simp] def Evm.pop (evm:Evm)(n:Nat)(r:n <= evm.stack.length) : Evm :=
  {stack := evm.stack.pop n r}

@[simp] def Evm.push (evm:Evm)(n:u256) : Evm :=
  {stack:=evm.stack.push n}

@[simp] def Evm.peek (evm:Evm)(n:Nat)(r:n < evm.stack.length) : u256 :=
  evm.stack.peek { val:= n, isLt := r}


def EmptyEvm : Evm := {stack:=[]}

/- =============================================================== -/
/- Execution -/
/- =============================================================== -/
inductive Exception where
| Revert
| StackUnderflow
| StackOverflow
| InvalidOpcode

inductive Outcome where
| Ok(evm: Evm)
| Done (gas: Nat)(data: Array u8)
| Error (err: Exception)

-- Map an outcome over a transition function.
@[simp] def Outcome.apply (out:Outcome)(fn:Evm->Outcome) : Outcome :=
  match out with
  | Outcome.Ok evm => (fn evm)
  | _ => out
