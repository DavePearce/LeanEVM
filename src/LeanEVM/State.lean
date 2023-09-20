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

-- Pop exactly one item of the EVM stack
@[simp] def EvmStack.pop1 (this:EvmStack)(_:this.length > 0) : EvmStack :=
  match this with
  | _::t => t

-- Simple lemma which states that the length of the stack after popping an item
-- has decreased by one.
def EvmStack.pop1_len (st:EvmStack)(r:st.length > 0) : st.length = (st.pop1 r).length + 1 :=
by
  match st with
  | _::t => simp

-- Unsure why this is needed exactly
def Nat.succ_ge {m:Nat}{n:Nat} (h:m + 1 >= n) : (n-1 <= m) :=
by
  rw [Nat.sub_le_iff_le_add]
  exact h

-- Pop an item of the EVM stack
def EvmStack.pop (this:EvmStack)(n:Nat)(r:this.length >= n) : EvmStack :=
  if p:n >= 1
  then
    let st := this.pop1 (by linarith);
    have w : this.length = st.length + 1 := (by apply pop1_len);
    have q : st.length + 1 >= n := (by linarith);
    EvmStack.pop st (n-1) (by apply Nat.succ_ge; exact q)
  else
    this
  decreasing_by
    simp_wf
    apply Nat.sub_lt_of_pos_le
    repeat simp [p]

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

@[simp] def Evm.pop (evm:Evm)(n:Nat)(r:evm.stack.length >= n) : Evm :=
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