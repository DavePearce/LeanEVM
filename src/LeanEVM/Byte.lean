import Mathlib.Tactic.Linarith

def byte := Fin 256

opaque BYTE_0 : byte := {val:=0, isLt:=(by simp)}

-- Construct a natural number from a sequence of one or more bytes store in big
-- endian form.
def from_bytes_be(bytes:Array byte)(i: Fin bytes.size) : Nat := 
  -- Read ith byte
  let b : byte := bytes[i];
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

example (n:Nat): [n][0] = n := 
by
  simp

-- Prove that converting an array consisting of a single byte generates the
-- corresponding Nat.
example (i:Fin 1)(b:byte): (from_bytes_be #[b] i) = b.val :=
by 
  have p:i=0 := by simp;
  unfold from_bytes_be
  --simp_arith
  simp [*]
  unfold Fin.val
  sorry  
  
  