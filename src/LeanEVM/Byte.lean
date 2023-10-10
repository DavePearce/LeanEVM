import Mathlib.Tactic.Linarith

def byte := Fin 256

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- Construct a natural number from a sequence of one or more bytes store in big
-- endian form.
def from_bytes_be(bytes:List byte)(i: Fin bytes.length) : Nat := 
  -- Read ith byte
  let b : byte := bytes[i];
  -- Decide what to do
  if r:i.val = 0 then b.val
  else
    -- Construct i-1
    let im1 : Fin bytes.length := {val:=i.val-1,isLt:=(
      by 
        have p : i.val-1 < i.val := (Nat.pred_lt r);
        linarith [i.isLt])
    };
    -- Done
    (256 * (from_bytes_be bytes im1)) + b.val

-- Prove that converting an array consisting of a single byte generates the
-- corresponding Nat.
example (n:byte)(i:Fin 1): (from_bytes_be [n] i) = n.val :=
by 
  let arr := [n];
  unfold from_bytes_be
  have p:i={val:=0,isLt:=(by simp)} := (by simp);  
  have q:i=0 := by sorry;
  have z:arr[0]=n := by sorry;
  rw [q]
  rw [<-z]
  simp_all
  sorry  