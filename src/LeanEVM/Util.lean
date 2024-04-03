import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import LeanEVM.Byte

/- =============================================================== -/
/- Constants -/
/- =============================================================== -/

def u4 := Fin 16

/- =============================================================== -/
/- U8 -/
/- =============================================================== -/

def u8 := Fin 256
opaque U8_0 : u8 := {val:=0, isLt:=(by simp)}

/- =============================================================== -/
/- U256 -/
/- =============================================================== -/

def TWO_256 := 0x10000000000000000000000000000000000000000000000000000000000000000

def u256 := Fin TWO_256

def u256.from_bytes(bytes:Array u8) : u256 :=
  let len : Nat := bytes.data.length;
  have p : len <= 32 := by sorry -- ASSUMPTION TO PROVE
  -- Convert bytes into nat
  let n := from_bytes_be bytes.data;
  -- Bound size of n using lemma
  have q : n < 256^32 := (from_bytes_be_bound 32 bytes.data p)
  -- Convert nat into u256
  {val:=n, isLt:=q}

def u256.add (i:u256)(j: u256) : u256 :=
  Fin.add i j

def u256.sub (i:u256)(j: u256) : u256 :=
  Fin.sub i j

def u256.mul (i:u256)(j: u256) : u256 :=
  Fin.mul i j

def u256.div (i:u256)(j: u256) : u256 :=
  Fin.div i j

def U256_0 : u256 := {val:=0, isLt:=(by simp_arith)}
def U256_1 : u256 := {val:=1, isLt:=(by simp_arith)}
def U256_2 : u256 := {val:=2, isLt:=(by simp_arith)}
def U256_3 : u256 := {val:=3, isLt:=(by simp_arith)}
def U256_4 : u256 := {val:=4, isLt:=(by simp_arith)}
def U256_MAX : u256 := {val:=TWO_256 - 1, isLt:=(by simp_arith)}

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

lemma fin_ofnat_lt (n:Nat)(m:Nat)(p:n<=m) : (Fin.ofNat (n:=m) n).val = n :=
by
  unfold Fin.ofNat
  have p: n % (m+1) = n := by sorry;
  simp [*]
  -- auto [p]

-- Simple demonstration that a singleton byte array returns its only byte as the
-- result.
example (n:byte)(m:u256)(p:n.val=m.val): (u256.from_bytes #[n]).val = m.val :=
by
  unfold u256.from_bytes
  simp
  unfold from_bytes_be
  rw [<-p]
  have q : n.val <= U256_MAX.val := (by sorry);
  --exact fin_ofnat_lt n.val U256_MAX.val q
  sorry
