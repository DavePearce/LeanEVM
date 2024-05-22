import LeanEVM.State
import LeanEVM.Eval
import LeanEVM.Instructions.Arithmetic
--import LeanEVM.Instructions.ControlFlow

def even (k : Nat) : Prop :=
  (k % 2) = 0

def test (k:Nat)(p:even k) : even (k+2) :=
by
  unfold even
  have q : (k+2) % 2 = k % 2 := Nat.add_mod_right k 2
  rw [q]
  exact p
