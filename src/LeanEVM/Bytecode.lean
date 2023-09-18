import LeanEVM.State
import LeanEVM.Util
import Mathlib.Tactic.Linarith

open Bytecode
open Exception
open Outcome

def ZERO : u256 := Fin.ofNat 0

def eval_stop (_: Evm) : Outcome :=
  Done 0 Array.empty

def eval_add (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : u256 := evm.peek 0 (by sorry);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := lhs.add rhs
    Ok (evm.push res)
  else
    Error StackUnderflow

def eval_push (evm: Evm)(n:u256) : Outcome :=
  Ok (evm.push n)

def eval_pop (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    Ok (evm.pop r)
  else
    Error StackUnderflow

def eval_dup (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    let val : u256 := evm.peek 0 (by simp [r]);
    Ok (evm.push val)
  else
    Error StackUnderflow

-- Execute a given bytecodes from a given state.
@[simp] def eval (evm: Evm) : Bytecode -> Outcome
| Bytecode.STOP => eval_stop evm
| Bytecode.ADD => eval_add evm
| Bytecode.POP => eval_pop evm
| Bytecode.DUP => eval_dup evm
| Bytecode.PUSH n => eval_push evm n

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
example (evm:Evm) : (eval_all [STOP] evm) = (Done 0 Array.empty) :=
by
  rfl

-- Executing ADD on an empty Evm produces a stack overflow.
example : (eval_all [ADD] EmptyEvm) = (Error StackUnderflow) :=
by
  simp

-- Executing ADD on Evm with two operands succeeds.
example (st:List u256): exists evm, (eval_all [ADD] {stack:=l::r::st}) = (Ok evm) :=
by
  exists {stack := (Fin.add l r)::st}
  sorry

-- Executing POP on Evm with at least one operand succeeds.
example (st:List u256)(p:st = v::rest): (eval_all [POP] {stack:=st}) = (Ok {stack:=rest}) :=
by
  simp [p]
  sorry

-- Executing PUSH then POP on an Evm is a no-op.
example (evm:Evm): (eval_all [PUSH n,POP] evm) = Ok evm :=
by
  simp [Evm.push, EvmStack.push, eval_all.reduce, eval_pop]
  sorry

-- Executing PUSH, PUSH, ADD on an Evm always succeeds.
example (evm:Evm): ∃nevm, (eval_all [PUSH N, PUSH m, ADD] evm) = Ok nevm :=
by
  simp
  sorry

-- def list_dec (l:List u256)(p:l.length > 0) : ∃ h t, l = h::t :=
-- by
--   match l with
--   | h::t => exists h,t
--   | [] => contradiction
