-- A simple proof useful when "left shifting" values.
def pow_shift(n:Nat)(m:Nat)(k:Nat)(p:n < m^k) : (m*n + m ≤ m^(k+1)) :=
by
  have q:(m*n + m = m*(n+1)) := by exact rfl
  rw [q,Nat.pow_add']
  simp
  exact Nat.mul_le_mul_left m p

-- A simple proof for "left shifting" bytes.  This could no doubt be generalised.
def pow256_shl(n:Nat)(m:UInt8)(k:Nat)(p:n < 256^k) : (256*n + m.val < 256^(k+1)) :=
by
  have s : 256*n + 256 ≤ 256^(k+1) := (pow_shift n 256 k p)
  have r : 256*n + m.val < 256*n + 256 := by exact Fin.natAdd.proof_1 (256 * n) m.val
  exact Nat.lt_of_lt_of_le r s

-- A simple proof for "right shifting" bytes.  This could no doubt be generalised.
def pow256_shr(n:Nat)(m:UInt8)(k:Nat)(p:n < 256^k) : (256^k * m.val + n < 256^(k+1)) :=
by
  have q1 : n + 255*256*k < (1+255)*256^k := sorry
  have q2 : n + 255*256*k < 256^k + 255*256^k := by simp at q1; sorry
  have q3 : n < 256^k := by exact p
  sorry
