
-- A set of zero or more bytes upto a given size.
structure FinVec {n:Nat} (T) where
  data : List T
  isLt : data.length <= n
