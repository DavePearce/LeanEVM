import LeanEVM.State

open Exception
open Outcome

-- ==================================================================
-- Stop
-- ==================================================================

-- Halt the machine without any return data
@[simp]
def STOP (_: Evm) : Outcome :=
  Done 0 Array.empty

-- Executing STOP on an arbitrary Evm produces Done.
example (evm:Evm) : (STOP evm) = (Done 0 Array.empty) :=
by
  rfl
