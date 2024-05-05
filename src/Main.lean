import LeanEVM.State

/- =============================================================== -/
/- Main -/
/- =============================================================== -/

def main : IO Unit :=
  IO.println "Hello world"


abbrev byte2 := Fin 256

def test(n:List byte2) := n.length

example : (test [1,2]) = 2 :=
by
  simp_arith
