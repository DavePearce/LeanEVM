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
| Dup

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