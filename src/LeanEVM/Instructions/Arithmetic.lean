import LeanEVM.State
import LeanEVM.Util.UInt

open Exception
open Outcome

-- ==================================================================
-- Add
-- ==================================================================

-- Unsigned integer addition with modulo arithmetic
@[simp]
def ADD (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs := evm.peek 0 (by omega);
    let rhs := evm.peek 1 (by simp [r]);
    let res := lhs + rhs;
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Executing ADD on an empty Evm produces a stack overflow.
example : (ADD EmptyEvm) = (Error StackUnderflow) :=
by
  simp_arith

-- Executing ADD on Evm with two operands succeeds.
example (rest:List UInt256): exists evm, (ADD {stack:=l::r::rest}) = (Ok evm) :=
by
  exists {stack := (Fin.add l r)::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- Test 1+2 = 3
example (rest:List UInt256): exists evm, (ADD {stack:=1::2::rest}) = (Ok evm) :=
by
  exists {stack := 3::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- Test max+1 = 0
example (rest:List UInt256): exists evm, (ADD {stack:=1::U256_MAX::rest}) = (Ok evm) :=
by
  simp_arith

-- ==================================================================
-- Sub
-- ==================================================================

-- Unsigned integer subtraction with modulo arithmetic
@[simp]
def SUB (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : UInt256 := evm.peek 0 (by omega);
    let rhs : UInt256 := evm.peek 1 (by simp [r]);
    let res : UInt256 := lhs - rhs;
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 0-1 = MAX
example (rest:List UInt256): exists evm, (SUB {stack:=0::1::rest}) = (Ok evm) :=
by
  exists {stack := U256_MAX::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- Test 3-1 = 2
example (rest:List UInt256): exists evm, (SUB {stack:=3::2::rest}) = (Ok evm) :=
by
  exists {stack := 1::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- ==================================================================
-- Mul
-- ==================================================================

-- Unsigned integer multiplication with modulo arithmetic
@[simp]
def MUL (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs := evm.peek 0 (by omega);
    let rhs := evm.peek 1 (by simp [r]);
    let res := lhs * rhs;
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 1*2 = 2
example (rest:List UInt256): exists evm, (MUL {stack:=1::2::rest}) = (Ok evm) :=
by
  exists {stack := 2::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- Test 2*2 = 4
example (rest:List UInt256): exists evm, (MUL {stack:=2::2::rest}) = (Ok evm) :=
by
  exists {stack := 4::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- ==================================================================
-- Div
-- ==================================================================

-- Unsigned integer division with modulo arithmetic
@[simp]
def DIV (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : UInt256 := evm.peek 0 (by omega);
    let rhs : UInt256 := evm.peek 1 (by simp [r]);
    let res : UInt256 := lhs / rhs;
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 4/2 = 2
example (rest:List UInt256): exists evm, (DIV {stack:=4::2::rest}) = (Ok evm) :=
by
  exists {stack := 2::rest}
  match rest with
  | h::t => rfl
  | [] => rfl

-- Test 1/0 = 0
example (rest:List UInt256): exists evm, (DIV {stack:=1::0::rest}) = (Ok evm) :=
by
  exists {stack := 0::rest}
  match rest with
  | h::t => rfl
  | [] => rfl
