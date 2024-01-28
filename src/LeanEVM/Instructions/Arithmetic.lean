import LeanEVM.State

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
    let lhs : u256 := evm.peek 0 (by linarith);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := (u256.add lhs rhs);
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
lemma AddOK(rest:List u256): exists evm, (ADD {stack:=l::r::rest}) = (Ok evm) :=
by
  exists {stack := (Fin.add l r)::rest}
  match rest with
  | h::t => simp; unfold u256.add; rfl
  | [] => simp; unfold u256.add; rfl

-- ==================================================================
-- Sub
-- ==================================================================

-- Unsigned integer subtraction with modulo arithmetic
@[simp]
def SUB (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : u256 := evm.peek 0 (by linarith);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := (u256.sub lhs rhs);
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 0-1 = MAX
example (rest:List u256): exists evm, (SUB {stack:=U256_0::U256_1::rest}) = (Ok evm) :=
by
  exists {stack := U256_MAX::rest}
  match rest with
  | h::t => simp; unfold u256.sub; rfl
  | [] => simp; unfold u256.sub; rfl

-- Test 3-1 = 2
example (rest:List u256): exists evm, (SUB {stack:=U256_3::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_1::rest}
  match rest with
  | h::t => simp; unfold u256.sub; rfl
  | [] => simp; unfold u256.sub; rfl

-- ==================================================================
-- Mul
-- ==================================================================

-- Unsigned integer multiplication with modulo arithmetic
@[simp]
def MUL (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : u256 := evm.peek 0 (by linarith);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := (u256.mul lhs rhs);
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 1*2 = 2
example (rest:List u256): exists evm, (MUL {stack:=U256_1::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_2::rest}
  match rest with
  | h::t => simp; unfold u256.mul; rfl
  | [] => simp; unfold u256.mul; rfl

-- Test 2*2 = 4
example (rest:List u256): exists evm, (MUL {stack:=U256_2::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_4::rest}
  match rest with
  | h::t => simp; unfold u256.mul; rfl
  | [] => simp; unfold u256.mul; rfl

-- ==================================================================
-- Div
-- ==================================================================

-- Unsigned integer division with modulo arithmetic
@[simp]
def DIV (evm: Evm) : Outcome :=
  if r:evm.stack.length > 1
  then
    let lhs : u256 := evm.peek 0 (by linarith);
    let rhs : u256 := evm.peek 1 (by simp [r]);
    let res : u256 := (u256.div lhs rhs);
    -- Take operands off stack
    let evm' := evm.pop 2 r;
    -- Push result on stack
    Ok (evm'.push res)
  else
    Error StackUnderflow

-- Test 4/2 = 2
example (rest:List u256): exists evm, (DIV {stack:=U256_4::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_2::rest}
  match rest with
  | h::t => simp; unfold u256.div; rfl
  | [] => simp; unfold u256.div; rfl

-- Test 1/0 = 0
example (rest:List u256): exists evm, (DIV {stack:=U256_1::U256_0::rest}) = (Ok evm) :=
by
  exists {stack := U256_0::rest}
  match rest with
  | h::t => simp; unfold u256.div; rfl
  | [] => simp; unfold u256.div; rfl
