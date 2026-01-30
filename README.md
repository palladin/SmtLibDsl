# SmtLibDsl

A **type-safe SMT-LIB DSL** for Lean 4 with Z3 integration.

## What is SmtLibDsl?

SmtLibDsl is a domain-specific language embedded in Lean 4 for writing SMT-LIB2 constraint programs. It provides:

- **Type-safe expressions** — Bitvector widths are tracked at compile time, preventing width mismatch errors
- **Free monad DSL** — Composable SMT commands using Lean's do-notation
- **SMT-LIB2 code generation** — Generates standards-compliant solver input
- **Z3 integration** — Solve constraints and parse results directly from Lean

## Quick Example

```lean
import SmtLibDsl

open SmtLibDsl.SMT

-- Find x where x + 1 = 10 (8-bit bitvector)
def findX : Smt Unit := do
  let x ← declareBV "x" 8
  assert (x +. bv 1 8 =. bv 10 8)

-- Compile to SMT-LIB2
#eval compile findX
/-
(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv10 8)))
(check-sat)
(get-model)
-/

-- Solve with Z3
#eval solve findX
-- Result: sat [(x, #x09)]
```

## Installation

### Prerequisites

- **Lean 4** / **Lake**: Install via [elan](https://github.com/leanprover/elan)
  ```bash
  curl https://elan-init.lean-lang.org/ -sSf | sh
  ```

- **Z3 SMT Solver**:
  ```bash
  # macOS
  brew install z3

  # Ubuntu/Debian
  sudo apt-get install z3
  ```

### Build

```bash
lake build
```

### Run Tests

```bash
lake exe smtlibdsl-test
```

### Configuration

| Environment Variable | Description | Default |
|---------------------|-------------|---------|
| `SMTLIBDSL_Z3_PATH` | Path to Z3 executable | `z3` (uses PATH) |

## DSL Reference

### Types

| Type | Description |
|------|-------------|
| `Ty.bool` | Boolean |
| `Ty.bitVec n` | Bitvector of width `n` |
| `Ty.array idxWidth elem` | Array with bitvector index |

### Declaring Variables

```lean
let x ← declareBV "x" 8           -- 8-bit bitvector
let b ← declareBool "b"           -- Boolean
let arr ← declareArray "a" 8 (ElemTy.bitVec 16)  -- Array
let grid ← declareBVTensor "cell" [9, 9] 4       -- 9×9 tensor of 4-bit values
```

### Operators

**Arithmetic** (width-preserving):
```lean
x +. y    -- addition
x -. y    -- subtraction
x *. y    -- multiplication
```

**Bitwise**:
```lean
x &. y    -- and
x |. y    -- or
x ^. y    -- xor
~. x      -- not
x <<. y   -- left shift
x >>. y   -- logical right shift
```

**Comparisons** (return `Expr Ty.bool`):
```lean
x =. y     -- equality
x <.ᵤ y    -- unsigned less-than
x ≤.ᵤ y    -- unsigned less-or-equal
x <.ₛ y    -- signed less-than
x ≤.ₛ y    -- signed less-or-equal
```

**Boolean**:
```lean
a ∧. b    -- and
a ∨. b    -- or
¬. a      -- not
a →. b    -- implication
```

**Arrays**:
```lean
selectArr arr idx        -- read
storeArr arr idx val     -- write (returns new array)
arr1 =.ₐ arr2           -- array equality
```

**Constraints**:
```lean
distinct [x, y, z]       -- all values are different
```

## Project Structure

```
SmtLibDsl/
├── SMT/
│   ├── Expr.lean      -- Type-indexed SMT expressions
│   ├── Cmd.lean       -- SMT commands & Smt monad
│   ├── Compile.lean   -- Compile to SMT-LIB2
│   ├── Solver.lean    -- Z3 integration
│   └── Tensor.lean    -- Multi-dimensional tensor support
Examples/
├── Sudoku.lean        -- 9×9 Sudoku solver
├── NQueens.lean       -- N-Queens puzzle
├── MagicSquare.lean   -- Magic square solver
├── Countdown.lean     -- Countdown numbers game
├── Minesweeper.lean   -- Minesweeper auto-solver
├── Sokoban.lean       -- Sokoban puzzle solver
├── Life.lean          -- Conway's Game of Life
└── Eternity2.lean     -- Edge-matching puzzle
Tests/
└── SMT.lean           -- Test suite
```

## Examples

### Sudoku Solver
```bash
lake exe sudoku
```
Uses 4-bit bitvectors for digits 1-9, with row/column/box distinctness constraints.

### N-Queens
```bash
lake exe nqueens
```
Places 8 queens on a chessboard with diagonal constraints using absolute difference.

### Magic Square
```bash
lake exe magicsquare
```
Finds an n×n grid where all rows, columns, and diagonals sum to the magic constant.

### Countdown Numbers Game
```bash
lake exe countdown
```
Synthesizes arithmetic expressions using RPN stack-based evaluation.

### Minesweeper
```bash
lake exe minesweeper
```
Iteratively deduces safe cells and mines using UNSAT queries.

### Sokoban
```bash
lake exe sokoban --list    # List available levels
lake exe sokoban 2         # Solve level 2
```
Finds move sequences to push boxes onto goals using state-space search.

## License

MIT License. See [LICENSE](LICENSE).
