import LeanEVM.Util.Bytes

/- =============================================================== -/
/- Constants -/
/- =============================================================== -/

def UInt4 := Fin 16

/- =============================================================== -/
/- U256 -/
/- =============================================================== -/

def TWO_256 := 0x10000000000000000000000000000000000000000000000000000000000000000

def UInt256 := Fin TWO_256

def UInt256.from_bytes(bytes: Bytes32) : UInt256 :=
  -- Convert bytes into nat
  let n := from_bytes_be bytes.data;
  -- Bound size of n using lemma
  have q : n < 256^32 := (from_bytes_be_bound 32 bytes.data bytes.isLt)
  -- Convert nat into UInt256
  {val:=n, isLt:=q}

def UInt256.add (i:UInt256)(j: UInt256) : UInt256 :=
  Fin.add i j

def UInt256.sub (i:UInt256)(j: UInt256) : UInt256 :=
  Fin.sub i j

def UInt256.mul (i:UInt256)(j: UInt256) : UInt256 :=
  Fin.mul i j

def UInt256.div (i:UInt256)(j: UInt256) : UInt256 :=
  Fin.div i j

def U256_0 : UInt256 := {val:=0, isLt:=(by simp_arith)}
def U256_1 : UInt256 := {val:=1, isLt:=(by simp_arith)}
def U256_2 : UInt256 := {val:=2, isLt:=(by simp_arith)}
def U256_3 : UInt256 := {val:=3, isLt:=(by simp_arith)}
def U256_4 : UInt256 := {val:=4, isLt:=(by simp_arith)}
def U256_MAX : UInt256 := {val:=TWO_256 - 1, isLt:=(by simp_arith)}

/- =============================================================== -/
/- Helpers -/
/- =============================================================== -/

-- Simple proof relating the size of a list to its structure.
def len_succ {a:Type} (h:a)(t:List a) : (h::t).length = t.length+1  :=
by
  induction t
  repeat simp

/- =============================================================== -/
/- Tests -/
/- =============================================================== -/

def fin_ofnat_lt (n:Nat)(m:Nat)(p:n<=m) : (Fin.ofNat (n:=m) n).val = n :=
by
  unfold Fin.ofNat
  have p: n % (m+1) = n := by sorry
  simp [*]
  -- auto [p]

-- Proof that a literal of length one has a length < 32.
def arr_len_lit1(n:byte) : #[n].data.length ≤ 32 :=
by
  simp

-- Simple demonstration that a singleton byte array returns its only byte as the
-- result.
example (n:UInt8)(bs:Bytes32)(p:bs.data=[n]): (UInt256.from_bytes bs).val = n.val :=
by
  unfold UInt256.from_bytes
  simp
  repeat unfold from_bytes_be
  --simp_arith
  sorry
