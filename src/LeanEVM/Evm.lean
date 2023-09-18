import LeanEVM.Util

/- =============================================================== -/
/- Bytecodes -/
/- =============================================================== -/

inductive Bytecode where
| STOP
| ADD
| PUSH(n:u256)
| POP
| DUP

/- =============================================================== -/
/- Ethereum Virtual Machine -/
/- =============================================================== -/
structure EVM where
  stack: (List u256)

def EmptyEVM : EVM := {stack:=[] }

/- =============================================================== -/
/- Execution -/
/- =============================================================== -/
inductive Exception where
| Revert
| StackUnderflow
| StackOverflow

inductive Outcome where
| Ok(evm: EVM)
| Done (gas: Nat)(data: Array u8)
| Error (err: Exception)
