import Mathlib.Tactic.Linarith
import LeanEVM.Util

/- =============================================================== -/
/- Bytecodes -/
/- =============================================================== -/

inductive Bytecode where
| Stop
| Add
| Push(n:u256)
| Pop
| Dup(n:u4)

@[simp]
def Dup_0 := Bytecode.Dup {val:=0, isLt:=(by simp)}
@[simp]
def Dup_1 := Bytecode.Dup {val:=1, isLt:=(by simp)}
@[simp]
def Dup_2 := Bytecode.Dup {val:=2, isLt:=(by simp)}
@[simp]
def Dup_3 := Bytecode.Dup {val:=3, isLt:=(by simp)}
@[simp]
def Dup_4 := Bytecode.Dup {val:=4, isLt:=(by simp)}
@[simp]
def Dup_5 := Bytecode.Dup {val:=5, isLt:=(by simp)}
@[simp]
def Dup_6 := Bytecode.Dup {val:=6, isLt:=(by simp)}
@[simp]
def Dup_7 := Bytecode.Dup {val:=7, isLt:=(by simp)}
@[simp]
def Dup_8 := Bytecode.Dup {val:=8, isLt:=(by simp)}
@[simp]
def Dup_9 := Bytecode.Dup {val:=9, isLt:=(by simp)}
@[simp]
def Dup_10 := Bytecode.Dup {val:=10, isLt:=(by simp)}
@[simp]
def Dup_11 := Bytecode.Dup {val:=11, isLt:=(by simp)}
@[simp]
def Dup_12 := Bytecode.Dup {val:=12, isLt:=(by simp)}
@[simp]
def Dup_13 := Bytecode.Dup {val:=13, isLt:=(by simp)}
@[simp]
def Dup_14 := Bytecode.Dup {val:=14, isLt:=(by simp)}
@[simp]
def Dup_15 := Bytecode.Dup {val:=15, isLt:=(by simp)}

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

inductive Outcome where
| Ok(evm: Evm)
| Done (gas: Nat)(data: Array u8)
| Error (err: Exception)