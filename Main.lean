import CogitoCore

open CogitoCore.SMT

/-- Example: Find x such that x + 1 = 10 (8-bit bitvector) -/
def findX : Smt Unit := do
  let x ← declareBV "x" 8
  assert (x +. bv 1 8 =. bv 10 8)
  checkSat
  getModel

/-- Example: Verify that x & (x - 1) clears the lowest set bit -/
def clearLowestBit : Smt Unit := do
  let x ← declareBV "x" 8
  let result ← declareBV "result" 8
  -- result = x & (x - 1)
  assert (result =. (x &. (x -. bv 1 8)))
  -- Check if there's any x where result has more bits set than x (should be unsat)
  checkSat
  getModel

def main : IO UInt32 := do
  IO.println s!"CogitoCore {CogitoCore.version}"
  IO.println ""

  IO.println "=== Example 1: Find x where x + 1 = 10 ==="
  IO.println "Generated SMT-LIB2:"
  IO.println (compile findX)
  IO.println "Solving with Z3..."
  let result1 ← solve findX
  IO.println s!"Result: {result1}"
  IO.println ""

  IO.println "=== Example 2: Clear lowest bit ==="
  IO.println "Generated SMT-LIB2:"
  IO.println (compile clearLowestBit)
  IO.println "Solving with Z3..."
  let result2 ← solve clearLowestBit
  IO.println s!"Result: {result2}"

  pure 0
