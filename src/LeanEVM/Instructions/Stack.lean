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
def Dup_1 := Bytecode.Dup {val:=0, isLt:=(by simp_arith)}
@[simp]
def Dup_2 := Bytecode.Dup {val:=1, isLt:=(by simp_arith)}
@[simp]
def Dup_3 := Bytecode.Dup {val:=2, isLt:=(by simp_arith)}
@[simp]
def Dup_4 := Bytecode.Dup {val:=3, isLt:=(by simp_arith)}
@[simp]
def Dup_5 := Bytecode.Dup {val:=4, isLt:=(by simp_arith)}
@[simp]
def Dup_6 := Bytecode.Dup {val:=5, isLt:=(by simp_arith)}
@[simp]
def Dup_7 := Bytecode.Dup {val:=6, isLt:=(by simp_arith)}
@[simp]
def Dup_8 := Bytecode.Dup {val:=7, isLt:=(by simp_arith)}
@[simp]
def Dup_9 := Bytecode.Dup {val:=8, isLt:=(by simp_arith)}
@[simp]
def Dup_10 := Bytecode.Dup {val:=9, isLt:=(by simp_arith)}
@[simp]
def Dup_11 := Bytecode.Dup {val:=10, isLt:=(by simp_arith)}
@[simp]
def Dup_12 := Bytecode.Dup {val:=11, isLt:=(by simp_arith)}
@[simp]
def Dup_13 := Bytecode.Dup {val:=12, isLt:=(by simp_arith)}
@[simp]
def Dup_14 := Bytecode.Dup {val:=13, isLt:=(by simp_arith)}
@[simp]
def Dup_15 := Bytecode.Dup {val:=14, isLt:=(by simp_arith)}
@[simp]
def Dup_16 := Bytecode.Dup {val:=15, isLt:=(by simp_arith)}

-- ==================================================================
-- Swap N
-- ==================================================================

@[simp]
def SWAP (evm: Evm)(n:u4) : Outcome :=
  if r:evm.stack.length > (n.val+1)
  then
    let v0 : u256 := evm.peek 0 (by linarith);
    let vn : u256 := evm.peek (n.val+1) (by simp [r]);
    -- Assign nth item to top position
    let evm' := evm.set 0 vn (by linarith);
    -- Assign top item to nth position
    Ok (evm'.set (n.val+1) v0 (by simp [r]))
  else
    Error StackUnderflow

@[simp]
def Swap_1 := Bytecode.Swap {val:=0, isLt:=(by simp_arith)}
@[simp]
def Swap_2 := Bytecode.Swap {val:=1, isLt:=(by simp_arith)}
@[simp]
def Swap_3 := Bytecode.Swap {val:=2, isLt:=(by simp_arith)}
@[simp]
def Swap_4 := Bytecode.Swap {val:=3, isLt:=(by simp_arith)}
@[simp]
def Swap_5 := Bytecode.Swap {val:=4, isLt:=(by simp_arith)}
@[simp]
def Swap_6 := Bytecode.Swap {val:=5, isLt:=(by simp_arith)}
@[simp]
def Swap_7 := Bytecode.Swap {val:=6, isLt:=(by simp_arith)}
@[simp]
def Swap_8 := Bytecode.Swap {val:=7, isLt:=(by simp_arith)}
@[simp]
def Swap_9 := Bytecode.Swap {val:=8, isLt:=(by simp_arith)}
@[simp]
def Swap_10 := Bytecode.Swap {val:=9, isLt:=(by simp_arith)}
@[simp]
def Swap_11 := Bytecode.Swap {val:=10, isLt:=(by simp_arith)}
@[simp]
def Swap_12 := Bytecode.Swap {val:=11, isLt:=(by simp_arith)}
@[simp]
def Swap_13 := Bytecode.Swap {val:=12, isLt:=(by simp_arith)}
@[simp]
def Swap_14 := Bytecode.Swap {val:=13, isLt:=(by simp_arith)}
@[simp]
def Swap_15 := Bytecode.Swap {val:=14, isLt:=(by simp_arith)}
@[simp]
def Swap_16 := Bytecode.Swap {val:=15, isLt:=(by simp_arith)}
