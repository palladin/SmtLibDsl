import CogitoCore

open CogitoCore.SMT

/-- Example: Find x such that x + 1 = 10 (8-bit bitvector) -/
def findX : Smt Unit := do
  let x ← declareBV "x" 8
  assert (x +. bv 1 8 =. bv 10 8)

/-- Example: Verify that x & (x - 1) clears the lowest set bit -/
def clearLowestBit : Smt Unit := do
  let x ← declareBV "x" 8
  let result ← declareBV "result" 8
  -- result = x & (x - 1)
  assert (result =. (x &. (x -. bv 1 8)))
  -- Check if there's any x where result has more bits set than x (should be unsat)

/-- Example: Declare a 2x3 tensor of 8-bit bitvectors and constrain their sum -/
def tensorExample : Smt Unit := do
  -- Declare a 2x3 matrix of 8-bit bitvectors: m_0_0, m_0_1, m_0_2, m_1_0, m_1_1, m_1_2
  -- matrix : Tensor [2, 3] (Expr (Ty.bitVec 8)) = Vect (Vect (Expr (Ty.bitVec 8)) 3) 2
  let matrix ← declareBVTensor "m" [2, 3] 8
  -- Access elements using bracket notation: matrix[row][col]
  let m_0_0 : Expr (Ty.bitVec 8) := matrix[0][0]
  let m_1_2 : Expr (Ty.bitVec 8) := matrix[1][2]
  -- Constrain first and last elements
  assert (m_0_0 =. bv 42 8)
  assert (m_1_2 =. bv 99 8)

def main : IO UInt32 := do
  IO.println s!"CogitoCore {CogitoCore.version}"
  IO.println ""

  IO.println "=== Example 1: Find x where x + 1 = 10 ==="
  IO.println "Generated SMT-LIB2:"
  IO.println (compile findX)
  IO.println "Solving with Z3..."
  let result1 ← solve findX
  IO.println s!"Result: {result1}"
  match result1 with
  | .sat model =>
    -- Use Model.get to extract typed value
    match model.get "x" (Ty.bitVec 8) with
    | some (xVal : BitVec 8) => IO.println s!"  x = {xVal.toNat} (decimal), 0x{xVal.toHex}"
    | none => IO.println "  Failed to parse x"
  | _ => pure ()
  IO.println ""

  IO.println "=== Example 2: Clear lowest bit ==="
  IO.println "Generated SMT-LIB2:"
  IO.println (compile clearLowestBit)
  IO.println "Solving with Z3..."
  let result2 ← solve clearLowestBit
  IO.println s!"Result: {result2}"
  match result2 with
  | .sat model =>
    match model.get "x" (Ty.bitVec 8), model.get "result" (Ty.bitVec 8) with
    | some (xVal : BitVec 8), some (resultVal : BitVec 8) =>
      IO.println s!"  x = {xVal.toNat}, result = {resultVal.toNat}"
    | _, _ => IO.println "  Failed to parse values"
  | _ => pure ()
  IO.println ""

  IO.println "=== Example 3: Tensor declaration (2x3 matrix) ==="
  IO.println "Generated SMT-LIB2:"
  IO.println (compile tensorExample)
  IO.println "Solving with Z3..."
  let result3 ← solve tensorExample
  IO.println s!"Result: {result3}"
  match result3 with
  | .sat model =>
    match model.get "m_0_0" (Ty.bitVec 8), model.get "m_1_2" (Ty.bitVec 8) with
    | some (m00 : BitVec 8), some (m12 : BitVec 8) =>
      IO.println s!"  m[0][0] = {m00.toNat}, m[1][2] = {m12.toNat}"
    | _, _ => IO.println "  Failed to parse tensor values"
  | _ => pure ()

  pure 0
