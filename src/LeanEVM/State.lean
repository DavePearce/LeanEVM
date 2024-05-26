import Batteries.Data.List.Lemmas
import LeanEVM.Util.UInt
set_option pp.numericTypes true
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
| Push(bs:Bytes32)
-- 80s: Duplication Operations
| Dup(n:UInt4)
-- 90s: Exchange Operations
| Swap(n:UInt4)
-- a0s: Logging Operations
-- f0s: System operations
| Invalid


/- =============================================================== -/
/- Code ROM -/
/- =============================================================== -/

def MAX_CODE_SIZE := 24576

def EvmCode := List UInt8

-- Read a byte at a given `pc` position within a code sequence.  If the position
-- is out-of-bounds, then `0` is returned.
@[simp]
def EvmCode.read(st:EvmCode)(pc:Nat) : UInt8 :=
  if r:pc >= st.length
  then
    0
  else
    st.get {val:=pc,isLt:=(by omega)}

-- Read `n` bytes from the code sequence starting a given `pc` position.
@[simp]
def EvmCode.slice(st:EvmCode)(pc:Nat)(n:Nat)(p:n≤32) : Bytes32 :=
  let head := (st.splitAt pc).snd
  let bytes := head.takeD n 0
  -- Prove bytes has at most 32 elements.
  have q : bytes.length = n := by sorry
  -- Construct FinVec
  {data:=bytes, isLt:=by exact le_of_eq_of_le q p}

-- Decode the instruction at a given `pc` position within the code sequence.
@[simp]
def EvmCode.decode (st:EvmCode)(pc:Nat) : Bytecode :=
  -- Read opcode
  let opcode := st.read pc;
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
  | 0x60 => Bytecode.Push (st.slice (pc+1) 1 (by simp_arith))
  | 0x61 => Bytecode.Push (st.slice (pc+1) 2 (by simp_arith))
  | 0x62 => Bytecode.Push (st.slice (pc+1) 3 (by simp_arith))
  | 0x63 => Bytecode.Push (st.slice (pc+1) 4 (by simp_arith))
  | 0x64 => Bytecode.Push (st.slice (pc+1) 5 (by simp_arith))
  | 0x65 => Bytecode.Push (st.slice (pc+1) 6 (by simp_arith))
  | 0x66 => Bytecode.Push (st.slice (pc+1) 7 (by simp_arith))
  | 0x67 => Bytecode.Push (st.slice (pc+1) 8 (by simp_arith))
  | 0x68 => Bytecode.Push (st.slice (pc+1) 9 (by simp_arith))
  | 0x69 => Bytecode.Push (st.slice (pc+1) 10 (by simp_arith))
  | 0x6a => Bytecode.Push (st.slice (pc+1) 11 (by simp_arith))
  | 0x6b => Bytecode.Push (st.slice (pc+1) 12 (by simp_arith))
  | 0x6c => Bytecode.Push (st.slice (pc+1) 13 (by simp_arith))
  | 0x6d => Bytecode.Push (st.slice (pc+1) 14 (by simp_arith))
  | 0x6e => Bytecode.Push (st.slice (pc+1) 15 (by simp_arith))
  | 0x6f => Bytecode.Push (st.slice (pc+1) 16 (by simp_arith))
  -- 80s: Duplication Operations
  | 0x80 => Bytecode.Dup {val:=0, isLt:=(by simp_arith)}
  | 0x81 => Bytecode.Dup {val:=1, isLt:=(by simp_arith)}
  | 0x82 => Bytecode.Dup {val:=2, isLt:=(by simp_arith)}
  | 0x83 => Bytecode.Dup {val:=3, isLt:=(by simp_arith)}
  | 0x84 => Bytecode.Dup {val:=4, isLt:=(by simp_arith)}
  | 0x85 => Bytecode.Dup {val:=5, isLt:=(by simp_arith)}
  | 0x86 => Bytecode.Dup {val:=6, isLt:=(by simp_arith)}
  | 0x87 => Bytecode.Dup {val:=7, isLt:=(by simp_arith)}
  | 0x88 => Bytecode.Dup {val:=8, isLt:=(by simp_arith)}
  | 0x89 => Bytecode.Dup {val:=9, isLt:=(by simp_arith)}
  | 0x8a => Bytecode.Dup {val:=10, isLt:=(by simp_arith)}
  | 0x8b => Bytecode.Dup {val:=11, isLt:=(by simp_arith)}
  | 0x8c => Bytecode.Dup {val:=12, isLt:=(by simp_arith)}
  | 0x8d => Bytecode.Dup {val:=13, isLt:=(by simp_arith)}
  | 0x8e => Bytecode.Dup {val:=14, isLt:=(by simp_arith)}
  | 0x8f => Bytecode.Dup {val:=15, isLt:=(by simp_arith)}
  -- 90s: Exchange Operations
  -- a0s: Logging Operations
  -- f0s: System operations
  | _ => Bytecode.Invalid

/- =============================================================== -/
/- Stack -/
/- =============================================================== -/
def EvmStack := List UInt256

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
@[simp] def EvmStack.push (st:EvmStack)(n:UInt256) : EvmStack :=
  n::st

-- Peek an item on the EVM stack
@[simp] def EvmStack.peek (st:EvmStack)(i:Fin st.length) : UInt256 :=
  st.get i

-- Assign an item v to the ith position in the EVM stack
@[simp] def EvmStack.set (st:EvmStack)(n:UInt256)(i:Fin st.length) : EvmStack :=
  List.set st i n

/- =============================================================== -/
/- Ethereum Virtual Machine -/
/- =============================================================== -/

structure Evm where
  stack: EvmStack

@[simp] def Evm.pop (evm:Evm)(n:Nat)(r:n <= evm.stack.length) : Evm :=
  {stack := evm.stack.pop n r}

@[simp] def Evm.push (evm:Evm)(n:UInt256) : Evm :=
  {stack:=evm.stack.push n}

@[simp] def Evm.peek (evm:Evm)(n:Nat)(r:n < evm.stack.length) : UInt256 :=
  evm.stack.peek { val:= n, isLt := r}

@[simp] def Evm.set (evm:Evm)(n:Nat)(v:UInt256)(r:n < evm.stack.length) : Evm :=
  {stack:=evm.stack.set v { val:= n, isLt := r}}

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
| Done (gas: Nat)(data: Array UInt8)
| Error (err: Exception)

-- Map an outcome over a transition function.
@[simp] def Outcome.apply (out:Outcome)(fn:Evm->Outcome) : Outcome :=
  match out with
  | Outcome.Ok evm => (fn evm)
  | _ => out

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

example : (EvmCode.decode [0x00] 0) = Bytecode.Stop :=
by
  rfl

example : (EvmCode.decode [0x00,0x01] 1) = Bytecode.Add :=
by
  rfl

example : (EvmCode.decode [0x60,0xf5] 0) = Bytecode.Push {data:=[0xf5],isLt:=by simp} :=
by
  rfl

example : (EvmCode.decode [0x61,0xf5] 0) = Bytecode.Push {data:=[0xf5,00],isLt:=by simp} :=
by
  rfl
