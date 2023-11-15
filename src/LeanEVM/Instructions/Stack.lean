import LeanEVM.State

open Exception
open Outcome

-- ==================================================================
-- Push N
-- ==================================================================

@[simp]
def PUSH (evm: Evm)(bs:Array u8) : Outcome :=
  -- Convert bytes into a word
  let w := u256.from_bytes bs;
  -- Push word
  Ok (evm.push w)

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

@[simp]
def Dup_1 := Bytecode.Dup {val:=0, isLt:=(by simp)}
@[simp]
def Dup_2 := Bytecode.Dup {val:=1, isLt:=(by simp)}
@[simp]
def Dup_3 := Bytecode.Dup {val:=2, isLt:=(by simp)}
@[simp]
def Dup_4 := Bytecode.Dup {val:=3, isLt:=(by simp)}
@[simp]
def Dup_5 := Bytecode.Dup {val:=4, isLt:=(by simp)}
@[simp]
def Dup_6 := Bytecode.Dup {val:=5, isLt:=(by simp)}
@[simp]
def Dup_7 := Bytecode.Dup {val:=6, isLt:=(by simp)}
@[simp]
def Dup_8 := Bytecode.Dup {val:=7, isLt:=(by simp)}
@[simp]
def Dup_9 := Bytecode.Dup {val:=8, isLt:=(by simp)}
@[simp]
def Dup_10 := Bytecode.Dup {val:=9, isLt:=(by simp)}
@[simp]
def Dup_11 := Bytecode.Dup {val:=10, isLt:=(by simp)}
@[simp]
def Dup_12 := Bytecode.Dup {val:=11, isLt:=(by simp)}
@[simp]
def Dup_13 := Bytecode.Dup {val:=12, isLt:=(by simp)}
@[simp]
def Dup_14 := Bytecode.Dup {val:=13, isLt:=(by simp)}
@[simp]
def Dup_15 := Bytecode.Dup {val:=14, isLt:=(by simp)}
@[simp]
def Dup_16 := Bytecode.Dup {val:=15, isLt:=(by simp)}
