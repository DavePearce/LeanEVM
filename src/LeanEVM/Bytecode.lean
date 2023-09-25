import LeanEVM.State
import LeanEVM.Util

open Bytecode
open Exception
open Outcome

-- ==================================================================
-- 0s: Stop and Arithmetic Operations
-- ==================================================================

-- Halt the machine without any return data
def STOP (_: Evm) : Outcome :=
  Done 0 Array.empty

-- Unsigned integer addition with modulo arithmetic
def ADD (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : u256 := evm.peek 0 (by linarith);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := (u256.add lhs rhs);
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- ==================================================================
-- 50s: Stack, Memory Storage and Flow Operations
-- ==================================================================

-- Pop word from stack
def POP (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    Ok (evm.pop 1 r)
  else
    Error StackUnderflow

-- ==================================================================
-- 60s & 70s: Push Operations
-- ==================================================================

def PUSH (evm: Evm)(n:u256) : Outcome :=
  Ok (evm.push n)

-- ==================================================================
-- 80s: Duplication Operations
-- ==================================================================

def DUP (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    let val : u256 := evm.peek 0 (by simp [r]);
    Ok (evm.push val)
  else
    Error StackUnderflow

-- ==================================================================
-- Eval(uate)
-- ==================================================================

-- Execute a given bytecodes from a given state.
@[simp] def eval (evm: Evm) : Bytecode -> Outcome
| Bytecode.Stop => STOP evm
| Bytecode.Add => ADD evm
| Bytecode.Pop => POP evm
| Bytecode.Dup => DUP evm
| Bytecode.Push n => PUSH evm n

-- Execute a sequence of zero or more bytecodes from a given state.
@[simp] def eval_all (code: List Bytecode)(evm:Evm) : Outcome :=
  reduce code (Ok evm)
where
   @[simp] reduce : (List Bytecode) -> Outcome -> Outcome
    | _,(Error err) => Error err
    | _,(Done gas data) => Done gas data
    | [],(Ok evm) => Ok evm
    | code::rest,(Ok evm) => reduce rest (eval evm code)

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

-- Executing STOP on an arbitrary Evm produces Done.
example (evm:Evm) : (eval_all [Stop] evm) = (Done 0 Array.empty) :=
by
  rfl

-- Executing ADD on an empty Evm produces a stack overflow.
example : (eval_all [Add] EmptyEvm) = (Error StackUnderflow) :=
by
  simp

-- Executing ADD on Evm with two operands succeeds.
example (rest:List u256): exists evm, (eval_all [Add] {stack:=l::r::rest}) = (Ok evm) :=
by
  exists {stack := (Fin.add l r)::rest}
  simp [*,ADD]
  unfold EvmStack.pop EvmStack.pop EvmStack.pop
  match rest with
  | h::t => simp; unfold u256.add; rfl
  | [] => simp; unfold u256.add; rfl

-- Executing POP on Evm with at least one operand succeeds.
example (st:List u256)(p:st = v::rest): (eval_all [Pop] {stack:=st}) = (Ok {stack:=rest}) :=
by
  simp [p]
  sorry

-- Executing PUSH then POP on an Evm is a no-op.
example (evm:Evm): (eval_all [Push n,Pop] evm) = Ok evm :=
by
  simp [Evm.push, EvmStack.push, eval_all.reduce, POP]
  sorry

-- Executing PUSH, PUSH, ADD on an Evm always succeeds.
example (evm:Evm): ∃nevm, (eval_all [Push N, Push m, Add] evm) = Ok nevm :=
by
  simp
  sorry

-- def list_dec (l:List u256)(p:l.length > 0) : ∃ h t, l = h::t :=
-- by
--   match l with
--   | h::t => exists h,t
--   | [] => contradiction
