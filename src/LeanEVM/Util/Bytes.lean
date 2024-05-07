import LeanEVM.Util.FinVec
import LeanEVM.Util.Lemmas

-- An array of (at most) 32 bytes.
def Bytes32 := FinVec (n:=32) UInt8

-- ==================================================================================
-- From Bytes (little endian)
-- ==================================================================================

-- Construct a natural number from a sequence of one or more bytes stored in little
-- endian form.
def from_bytes_le(bytes:List UInt8) : Nat :=
  match bytes with
  | List.nil => 0
  | b::bs =>
      (256 * (from_bytes_le bs)) + b.toNat

-- Bound the number returned by `from_bytes_le`.  For example, if one byte is
-- passed into `from_bytes_le` then the return value is bounded by `256`;
-- likewise, if two bytes are passed into `from_bytes_le` then the return value
-- is bounded by `65536`, etc.
def from_bytes_le_bound(bytes:List UInt8) : (from_bytes_le bytes) < 256^bytes.length :=
by
  match bytes with
  | [] => simp_arith
  | b::bs =>
      apply pow256_shl
      apply (from_bytes_le_bound bs)

-- Prove correct translation for sequence of length 1.
example (n:UInt8): (from_bytes_le [n]) = n.val :=
by
  repeat unfold from_bytes_le
  simp
  rfl

-- Prove correct translation for simple sequence of length 2.
example (n:UInt8): (from_bytes_le [n, 0]) = n.val :=
by
  repeat unfold from_bytes_le
  simp
  rfl

-- Prove correct translation for arbitrary sequence of length 2.
example (m:UInt8)(n:UInt8): (from_bytes_le [m, n]) = m.val + (256*n.val) :=
by
  repeat unfold from_bytes_le
  unfold UInt8.toNat
  simp_arith

-- ==================================================================================
-- From Bytes (big endian)
-- ==================================================================================

-- Construct a natural number from a sequence of one or more bytes stored in big
-- endian form.
def from_bytes_be(bytes:List UInt8) : Nat :=
  match bytes with
  | List.nil => 0
  | b::bs =>
      let n := bs.length
      ((256^n) * b.toNat) + (from_bytes_be bs)

-- Bound the number returned by `from_bytes_be`.  For example, if one byte is
-- passed into `from_bytes_le` then the return value is bounded by `256`;
-- likewise, if two bytes are passed into `from_bytes_be` then the return value
-- is bounded by `65536`, etc.
def from_bytes_be_bound(bytes:List UInt8) : (from_bytes_be bytes) < 256^bytes.length :=
by
  match bytes with
  | [] => simp_arith
  | b::bs =>
      apply pow256_shr
      apply (from_bytes_be_bound bs)

-- Prove correct translation for sequence of length 1.
example (n:UInt8): (from_bytes_be [n]) = n.val :=
by
  repeat unfold from_bytes_be
  unfold UInt8.toNat
  simp_arith

-- Prove correct translation for simple sequence of length 2.
example (n:UInt8): (from_bytes_be [0, n]) = n.val :=
by
  repeat unfold from_bytes_be
  unfold UInt8.toNat
  simp_arith

-- Prove correct translation for arbitrary sequence of length 2.
example (m:UInt8)(n:UInt8): (from_bytes_be [m, n]) = (256*m.val) + n.val :=
by
  repeat unfold from_bytes_be
  unfold UInt8.toNat
  simp_arith
