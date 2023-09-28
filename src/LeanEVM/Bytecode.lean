import LeanEVM.State
import LeanEVM.Util

open Bytecode
open Exception
open Outcome

-- ==================================================================
-- 0s: Stop and Arithmetic Operations
-- ==================================================================

-- Halt the machine without any return data
@[simp]
def STOP (_: Evm) : Outcome :=
  Done 0 Array.empty

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


-- ==================================================================
-- 50s: Stack, Memory Storage and Flow Operations
-- ==================================================================

-- Pop word from stack
@[simp]
def POP (evm: Evm) : Outcome :=
  if r:evm.stack.length > 0
  then
    Ok (evm.pop 1 r)
  else
    Error StackUnderflow

-- ==================================================================
-- 60s & 70s: Push Operations
-- ==================================================================

@[simp]
def PUSH (evm: Evm)(n:u256) : Outcome :=
  Ok (evm.push n)

-- ==================================================================
-- 80s: Duplication Operations
-- ==================================================================

@[simp]
def DUP (evm: Evm)(n:u4) : Outcome :=
  if r:evm.stack.length > n.val
  then
    let val : u256 := evm.peek n.val (by simp [r]);
    Ok (evm.push val)
  else
    Error StackUnderflow

-- ==================================================================
-- Eval(uate)
-- ==================================================================

-- Execute a given bytecodes from a given state.
@[simp]
def eval (evm: Evm) : Bytecode -> Outcome
| Bytecode.Stop => STOP evm
| Bytecode.Add => ADD evm
| Bytecode.Sub => SUB evm
| Bytecode.Mul => MUL evm
| Bytecode.Div => DIV evm
| Bytecode.Pop => POP evm
| Bytecode.Dup n => DUP evm n
| Bytecode.Push n => PUSH evm n

-- Execute a sequence of zero or more bytecodes from a given state.
@[simp]
def eval_all (code: List Bytecode)(evm:Evm) : Outcome :=
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
  match rest with
  | h::t => simp; unfold u256.add; rfl
  | [] => simp; unfold u256.add; rfl

-- Test 0-1 = MAX
example (rest:List u256): exists evm, (eval_all [Sub] {stack:=U256_0::U256_1::rest}) = (Ok evm) :=
by
  exists {stack := U256_MAX::rest}
  match rest with
  | h::t => simp; unfold u256.sub; rfl
  | [] => simp; unfold u256.sub; rfl

-- Test 3-1 = 2
example (rest:List u256): exists evm, (eval_all [Sub] {stack:=U256_3::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_1::rest}
  match rest with
  | h::t => simp; unfold u256.sub; rfl
  | [] => simp; unfold u256.sub; rfl  

-- Test 1*2 = 2
example (rest:List u256): exists evm, (eval_all [Mul] {stack:=U256_1::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_2::rest}
  match rest with
  | h::t => simp; unfold u256.mul; rfl
  | [] => simp; unfold u256.mul; rfl

-- Test 2*2 = 4
example (rest:List u256): exists evm, (eval_all [Mul] {stack:=U256_2::U256_2::rest}) = (Ok evm) :=
by
  exists {stack := U256_4::rest}
  match rest with
  | h::t => simp; unfold u256.mul; rfl
  | [] => simp; unfold u256.mul; rfl


-- Executing POP on Evm with at least one operand succeeds.
example (st:List u256)(p:st = v::rest): (eval_all [Pop] {stack:=st}) = (Ok {stack:=rest}) :=
by
  simp [p]
  match rest with
  | h::t => simp
  | [] => simp

-- Executing PUSH then POP on an Evm is a no-op.
example (evm:Evm): (eval_all [Push n,Pop] evm) = Ok evm :=
by
  match evm with
  | {stack:=h::t} => simp
  | {stack:=[]} => simp

-- Executing PUSH, PUSH, ADD on an Evm always succeeds.
example (evm:Evm): ∃evm', (eval_all [Push n, Push m, Add] evm) = Ok evm' :=
by
  simp

-- Executing DUP0 has the right effect
example (evm:Evm): ∃evm', (eval_all [Push n, Dup_0] evm) = (Ok evm') :=
by
  exists {stack := n::n::evm.stack}
  simp [*]

-- Executing DUP1 has the right effect
example (evm:Evm): ∃evm', (eval_all [Push n, Push m, Dup_1] evm) = (Ok evm') :=
by
  exists {stack := n::m::n::evm.stack}
  simp [*]

-- Executing DUP2 has the right effect
example (evm:Evm): ∃evm', (eval_all [Push n, Push m, Push l, Dup_2] evm) = (Ok evm') :=
by
  exists {stack := n::l::m::n::evm.stack}
  -- Unnecessary?
  have p : 2 < Nat.succ (Nat.succ (Nat.succ (List.length evm.stack))) := by linarith
  simp [*]

-- def list_dec (l:List u256)(p:l.length > 0) : ∃ h t, l = h::t :=
-- by
--   match l with
--   | h::t => exists h,t
--   | [] => contradiction
