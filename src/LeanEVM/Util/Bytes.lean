import LeanEVM.Util.FinVec
import LeanEVM.Util.Lemmas

def byte := Fin 256

def Bytes32 := FinVec (n:=32) byte

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- ==================================================================================
-- From Bytes (little endian)
-- ==================================================================================

-- Construct a natural number from a sequence of one or more bytes stored in little
-- endian form.
def from_bytes_le(bytes:List byte) : Nat :=
  match bytes with
  | List.nil => 0
  | b::bs =>
      (256 * (from_bytes_le bs)) + b.val

-- Bound the number returned by `from_bytes_le`.  For example, if one byte is
-- passed into `from_bytes_le` then the return value is bounded by `256`;
-- likewise, if two bytes are passed into `from_bytes_le` then the return value
-- is bounded by `65536`, etc.
def from_bytes_le_bound(n:Nat)(bytes:List byte)(p:bytes.length ≤ n) : (from_bytes_le bytes) < 256^n :=
by
  match n,bytes with
  | 0, [] => unfold from_bytes_le; simp
  | k+1, [] =>
      have q : 0 ≤ k := by simp
      have r : (from_bytes_le []) < 256^k := (by apply from_bytes_le_bound k [] q)
      have s : 256^k < 256^(k+1) := by apply Nat.pow_lt_pow_succ; simp
      exact Nat.lt_trans r s
  | k+1, b::bs =>
      have q : bs.length ≤ k := by unfold List.length at p; exact Nat.le_of_lt_succ p
      have r : (from_bytes_le bs) < 256^k := (by apply from_bytes_le_bound k bs q)
      unfold from_bytes_le
      apply (pow256_shift (from_bytes_le bs) b k r)

example (n:byte): (from_bytes_le [n]) = n.val :=
by
  repeat unfold from_bytes_le
  simp

example (n:byte): (from_bytes_le [n, Fin.ofNat 0]) = n.val :=
by
  repeat unfold from_bytes_le
  unfold Fin.ofNat
  simp

-- ==================================================================================
-- From Bytes (big endian)
-- ==================================================================================

-- Construct a natural number from a sequence of one or more bytes stored in big
-- endian form.
def from_bytes_be(bytes:List byte) : Nat :=
  from_bytes_le (List.reverse bytes)

-- Bound the number returned by `from_bytes_be`.  For example, if one byte is
-- passed into `from_bytes_le` then the return value is bounded by `256`;
-- likewise, if two bytes are passed into `from_bytes_be` then the return value
-- is bounded by `65536`, etc.
def from_bytes_be_bound(n:Nat)(bytes:List byte)(p:bytes.length ≤ n) : (from_bytes_be bytes) < 256^n :=
by
  sorry

example (n:byte): (from_bytes_be [n]) = n.val :=
by
  unfold from_bytes_be
  simp
  repeat unfold from_bytes_le
  simp

example (n:byte): (from_bytes_be [Fin.ofNat 0, n]) = n.val :=
by
  unfold from_bytes_be
  repeat simp; unfold from_bytes_le
  unfold Fin.ofNat
  simp_arith
