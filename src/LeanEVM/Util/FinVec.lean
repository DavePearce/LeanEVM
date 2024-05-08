
-- A set of zero or more bytes upto a given size.
structure FinVec {n:Nat} (T) where
  data : List T
  isLt : data.length <= n

-- Determine length of this vector
def FinVec.length {n:Nat} (v:FinVec (n:=n) T) :=
  v.data.length
