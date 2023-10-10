import Mathlib.Tactic.Linarith
import LeanEVM.Byte

def Nat.zero_lt (n:Nat)(p:n ≠ 0) : 0 < n :=
by
  match n with
  | Nat.zero => contradiction
  | Nat.succ m => simp

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
  -- Check for base case
  if p:len <= 0 then Fin.ofNat 0
  else
    -- Construct starting index (i.e. zero)
    let i : (Fin len) := {val:=0,isLt:=(by linarith)};
    -- Convert bytes into nat
    let n := from_bytes_be bytes.data i;
    -- Convert nat into u256
    Fin.ofNat n

def u256.add (i:u256)(j: u256) : u256 :=
  Fin.add i j

def u256.sub (i:u256)(j: u256) : u256 :=
  Fin.sub i j

def u256.mul (i:u256)(j: u256) : u256 :=
  Fin.mul i j

def u256.div (i:u256)(j: u256) : u256 :=
  Fin.div i j

def U256_0 : u256 := {val:=0, isLt:=(by simp)}
def U256_1 : u256 := {val:=1, isLt:=(by simp)}
def U256_2 : u256 := {val:=2, isLt:=(by simp)}
def U256_3 : u256 := {val:=3, isLt:=(by simp)}
def U256_4 : u256 := {val:=4, isLt:=(by simp)}
def U256_MAX : u256 := {val:=TWO_256 - 1, isLt:=(by simp)}

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

-- Simple demonstration that a singleton byte array returns its only byte as the
-- result.
example (n:byte)(m:u256)(p:n.val=m.val): (u256.from_bytes #[n]) = m :=
by 
  unfold u256.from_bytes
  simp
  unfold from_bytes_be
  simp  
  sorry  