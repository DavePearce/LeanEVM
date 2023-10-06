import LeanEVM.State

open Exception
open Outcome

-- ==================================================================
-- Push N
-- ==================================================================

@[simp]
def PUSH (evm: Evm)(n:u256) : Outcome :=
  Ok (evm.push n)

-- ==================================================================
-- Pop
-- ==================================================================

-- Pop word from stack
@[simp]
def POP (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    Ok (evm.pop 1 r)
  else
    Error StackUnderflow

-- Executing POP on Evm with at least one operand succeeds.
lemma PopOK (st:List u256)(p:st = v::rest): (POP {stack:=st}) = (Ok {stack:=rest}) :=
by
  simp [p]
  match rest with
  | h::t => simp
  | [] => simp

-- Executing PUSH then POP on an Evm is a no-op.
example (evm:Evm): ((PUSH evm n).apply POP) = Ok evm :=
by
  match evm with
  | {stack:=h::t} => simp
  | {stack:=[]} => simp

-- ==================================================================
-- Dup N
-- ==================================================================

@[simp]
def DUP (evm: Evm)(n:u4) : Outcome :=
  if r:evm.stack.length > n.val
  then
    let val : u256 := evm.peek n.val (by simp [r]);
    Ok (evm.push val)
  else
    Error StackUnderflow
