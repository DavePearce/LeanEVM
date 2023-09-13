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

def eval_pop (evm: EVM) : Outcome :=
  match evm.stack with
  | _::rest => Ok { stack := rest }
  | [] => Error StackUnderflow

def eval_dup (evm: EVM) : Outcome :=
  match evm.stack with
  | l::rest => Ok { stack := l::l::rest }
  | [] => Error StackUnderflow

-- Execute a given bytecodes from a given state.
def eval (evm: EVM) : Bytecode -> Outcome
| Bytecode.STOP => eval_stop evm
| Bytecode.ADD => eval_add evm
| Bytecode.POP => eval_pop evm
| Bytecode.DUP => eval_dup evm

-- Execute a sequence of zero or more bytecodes from a given state.
def eval_all (code: List Bytecode)(evm:EVM) : Outcome :=
  reduce code (Ok evm)
where
   reduce : (List Bytecode) -> Outcome -> Outcome
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
  unfold eval_all eval_all.reduce eval_all.reduce
  unfold eval eval_add
  unfold EmptyEVM
  simp









