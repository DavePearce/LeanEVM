import LeanEVM.Util.FinVec
import LeanEVM.Util.Lemmas

def byte := Fin 256

def Bytes32 := FinVec (n:=32) byte

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- Construct a natural number from a sequence of one or more bytes stored in big
-- endian form.
def from_bytes_be(bytes:List byte) : Nat :=
  match bytes with
  | List.nil => 0
  | b::bs =>
      (256 * (from_bytes_be bs)) + b.val

-- Bound the number returned by `from_bytes_be`.  For example, if one byte is
-- passed into `from_bytes_be` then the return value is bounded by `256`;
-- likewise, if two bytes are passed into `from_bytes_be` then the return value
-- is bounded by `65536`, etc.
def from_bytes_be_bound(n:Nat)(bytes:List byte)(p:bytes.length ≤ n) : (from_bytes_be bytes) < 256^n :=
by
  match n,bytes with
  | 0, [] => unfold from_bytes_be; simp
  | k+1, [] =>
      have q : 0 ≤ k := by simp
      have r : (from_bytes_be []) < 256^k := (by apply from_bytes_be_bound k [] q)
      have s : 256^k < 256^(k+1) := by apply Nat.pow_lt_pow_succ; simp
      exact Nat.lt_trans r s
  | k+1, b::bs =>
      have q : bs.length ≤ k := by unfold List.length at p; exact Nat.le_of_lt_succ p
      have r : (from_bytes_be bs) < 256^k := (by apply from_bytes_be_bound k bs q)
      unfold from_bytes_be
      apply (pow256_shift (from_bytes_be bs) b k r)

-- Prove that converting an array consisting of a single byte generates the
-- corresponding Nat.
example (n:byte): (from_bytes_be [n]) = n.val :=
by
  repeat unfold from_bytes_be; simp
  sorry
