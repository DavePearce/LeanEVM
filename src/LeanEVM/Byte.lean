import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

def byte := Fin 256

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- Construct a natural number from a sequence of one or more bytes store in big
-- endian form.
def from_bytes_be(bytes:List byte)(i: Fin bytes.length) : Nat :=
  match bytes, i with
  | b::_, {val:=0,isLt:=_} => b.val
  | b::bs, {val:=k+1,isLt:=p} =>
      have q : k < bs.length := by exact Nat.succ_lt_succ_iff.mp p
      let im1 : Fin bs.length := {val:= k, isLt:=by exact q}
      (256 * (from_bytes_be bs im1)) + b.val

-- Prove that converting an array consisting of a single byte generates the
-- corresponding Nat.
example (n:byte)(i:Fin 1): (from_bytes_be [n] i) = n.val :=
by
  match i with
  | 0 => rfl
