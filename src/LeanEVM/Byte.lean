import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch

def byte := Fin 256

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- Construct a natural number from a sequence of one or more bytes stored in big
-- endian form.
def from_bytes_be(bytes:List byte) : Nat :=
  match bytes with
  | List.nil => 0
  | b::bs =>
      (256 * (from_bytes_be bs)) + b.val

-- Bound size of number returned by `from_bytes_be`.
lemma from_bytes_be_bound(n:Nat)(bytes:List byte)(p:bytes.length ≤ n) : (from_bytes_be bytes) < 256^n :=
by
  match bytes with
  | List.nil => unfold from_bytes_be; simp
  | b::bs =>
      have p := from_bytes_be_bound n bs
      unfold from_bytes_be
      --unfold List.length
      sorry

-- Prove that converting an array consisting of a single byte generates the
-- corresponding Nat.
example (n:byte): (from_bytes_be [n]) = n.val :=
by
  repeat unfold from_bytes_be; simp
