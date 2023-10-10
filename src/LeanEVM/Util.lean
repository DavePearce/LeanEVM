import Mathlib.Tactic.Linarith

/- =============================================================== -/
/- Constants -/
/- =============================================================== -/

def u4 := Fin 16

/- =============================================================== -/
/- U8 -/
/- =============================================================== -/

def u8 := Fin 256

-- Construct a natural number from a sequence of one or more bytes.
def from_bytes_be(bytes:Array u8)(i: Fin bytes.size) : Nat := 
  -- Read ith byte
  let b : u8 := (bytes.get i);
  -- Decide what to do
  if r:i.val = 0 then b.val
  else
    -- Construct i-1
    let im1 : Fin bytes.size := {val:=i.val-1,isLt:=(
      by 
        have p : i.val-1 < i.val := (Nat.pred_lt r);
        linarith [i.isLt])
    };
    -- Done
    (256 * (from_bytes_be bytes im1)) + b.val
  termination_by
    from_bytes_be _ i => (i.val)  

opaque U8_0 : u8 := {val:=0, isLt:=(by simp)}

/- =============================================================== -/
/- U256 -/
/- =============================================================== -/

def TWO_256 := 0x10000000000000000000000000000000000000000000000000000000000000000

def u256 := Fin TWO_256
    
def u256.from_bytes(bytes:Array u8) : u256 := 
  if bytes.size == 0 then {val:=0, isLt:=(by simp)}
  else
    sorry  

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