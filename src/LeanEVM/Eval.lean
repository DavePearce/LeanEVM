import LeanEVM.State
import LeanEVM.Util
import LeanEVM.Instructions.Arithmetic
import LeanEVM.Instructions.ControlFlow
import LeanEVM.Instructions.Stack

open Bytecode
open Exception
open Outcome

-- ==================================================================
-- Eval(uate)
-- ==================================================================

-- Execute a given bytecodes from a given state.
@[simp]
def dispatch (evm: Evm) : Bytecode -> Outcome
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
def eval (code: List Bytecode)(evm:Evm) : Outcome :=
  reduce code (Ok evm)
where
   @[simp] reduce : (List Bytecode) -> Outcome -> Outcome
    | _,(Error err) => Error err
    | _,(Done gas data) => Done gas data
    | [], o => o
    | code::rest,(Ok evm) => reduce rest (dispatch evm code)

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

-- Executing PUSH then POP on an Evm is a no-op.
example (evm:Evm): (eval [Push n,Pop] evm) = Ok evm :=
by
  match evm with
  | {stack:=h::t} => simp
  | {stack:=[]} => simp

-- Executing PUSH, PUSH, ADD on an Evm always succeeds.
example (evm:Evm): ∃evm', (eval [Push n, Push m, Add] evm) = Ok evm' :=
by
  simp

-- Executing DUP0 has the right effect
example (evm:Evm): ∃evm', (eval [Push n, Dup_0] evm) = (Ok evm') :=
by
  exists {stack := n::n::evm.stack}
  simp [*]

-- Executing DUP1 has the right effect
example (evm:Evm): ∃evm', (eval [Push n, Push m, Dup_1] evm) = (Ok evm') :=
by
  exists {stack := n::m::n::evm.stack}
  simp [*]

-- Executing DUP2 has the right effect
example (evm:Evm): ∃evm', (eval [Push n, Push m, Push l, Dup_2] evm) = (Ok evm') :=
by
  exists {stack := n::l::m::n::evm.stack}
  simp [*]  
  simp_arith