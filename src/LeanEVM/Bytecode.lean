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
  | [l,r]++rest => let v : u256 := Fin.add l r; Ok { stack := [v] ++ rest }
  | _ => Error StackUnderflow

def eval_pop (evm: EVM) : Outcome :=
  match evm.stack with
  | [_]++rest => Ok { stack := rest }
  | _ => Error StackUnderflow

def eval_dup (evm: EVM) : Outcome :=
  match evm.stack with
  | [l]++rest => Ok { stack := [l] ++ rest }
  | _ => Error StackUnderflow

-- Execute a given bytecodes from a given state.
def eval (evm: EVM) : Bytecode -> Outcome
| Bytecode.STOP => eval_stop evm
| Bytecode.ADD => eval_add evm
| Bytecode.POP => eval_pop evm
| Bytecode.DUP => eval_dup evm

-- Execute a sequence of zero or more bytecodes from a given state.
def eval_all (codes: List Bytecode)(st: Outcome) : Outcome :=
  match (st,codes) with
  | (Error _err, _) => st
  | (Done _gas _data, _) => st
  | (Ok evm, [code]++rest) => eval_all rest (eval evm code)
  | (Ok evm, []) => st
  decreasing_by
    simp_wf
    sorry

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

-- Executing STOP on an arbitrary EVM produces Done.
example (evm:EVM) : (eval_all [STOP] (Ok evm)) = (Done 0 Array.empty) :=
by
  simp_wf
  sorry
