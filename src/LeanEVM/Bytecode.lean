import LeanEVM.Evm
import LeanEVM.Util
import Mathlib.Tactic.Linarith

open Bytecode
open Exception
open Outcome

def eval_stop (_: EVM) : Outcome :=
  Done 0 Array.empty

def eval_add (evm: EVM) : Outcome :=
  match evm.stack with
  | l::r::rest => let v : u256 := Fin.add l r; Ok { stack := v::rest }
  | [_] => Error StackUnderflow
  | [] => Error StackUnderflow

def eval_push (evm: EVM)(n:u256) : Outcome :=
  Ok {stack:=n::evm.stack}

def eval_pop (evm: EVM) : Outcome :=
  match evm.stack with
  | _::rest => Ok { stack := rest }
  | [] => Error StackUnderflow

def eval_dup (evm: EVM) : Outcome :=
  match evm.stack with
  | l::rest => Ok { stack := l::l::rest }
  | [] => Error StackUnderflow

-- Execute a given bytecodes from a given state.
@[simp] def eval (evm: EVM) : Bytecode -> Outcome
| Bytecode.STOP => eval_stop evm
| Bytecode.ADD => eval_add evm
| Bytecode.POP => eval_pop evm
| Bytecode.DUP => eval_dup evm
| Bytecode.PUSH n => eval_push evm n

-- Execute a sequence of zero or more bytecodes from a given state.
@[simp] def eval_all (code: List Bytecode)(evm:EVM) : Outcome :=
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

-- Executing STOP on an arbitrary EVM produces Done.
example (evm:EVM) : (eval_all [STOP] evm) = (Done 0 Array.empty) :=
by
  rfl

-- Executing ADD on an empty EVM produces a stack overflow.
example : (eval_all [ADD] EmptyEVM) = (Error StackUnderflow) :=
by
  simp

-- Executing ADD on EVM with two operands succeeds.
example (st:List u256): exists evm, (eval_all [ADD] {stack:=l::r::st}) = (Ok evm) :=
by
  exists {stack := (Fin.add l r)::st}

-- Executing POP on EVM with at least one operand succeeds.
example (st:List u256)(p:st = v::rest): (eval_all [POP] {stack:=st}) = (Ok {stack:=rest}) :=
by
  simp [p]

-- Executing PUSH then POP on an EVM is a no-op.
example (evm:EVM): (eval_all [PUSH n,POP] evm) = Ok evm :=
by
  simp

-- Executing PUSH, PUSH, ADD on an EVM always succeeds.
example (evm:EVM): ∃nevm, (eval_all [PUSH N, PUSH m, ADD] evm) = Ok nevm :=
by
  simp

def list_dec (l:List u256)(p:l.length > 0) : exists h, exists t, l = h::t :=
by
  match l with
  | h::t => exists h,t
  | [] => contradiction
