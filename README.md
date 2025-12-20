# CogitoCore

An experimental AI project exploring the combination of **dependently-typed Lean DSL for SMT-LIB** with **Z3** and **powerful LLMs** to solve challenging reasoning puzzles and problems.

## The Idea

CogitoCore leverages the strengths of multiple paradigms:

- **Lean 4**: A dependently-typed functional programming language that enables precise, type-safe specifications
- **SMT-LIB / Z3**: Industry-standard satisfiability modulo theories solver for automated reasoning
- **Large Language Models**: AI-powered understanding and problem decomposition

By combining formal verification techniques with modern AI capabilities, CogitoCore aims to tackle complex logical reasoning tasks that neither approach could solve alone.

## Features

- **Type-safe SMT expressions**: Bitvector width and types are tracked at compile time
- **Free monad DSL**: Composable SMT commands with do-notation
- **SMT-LIB2 output**: Generate standards-compliant solver input
- **Z3 integration**: Solve constraints directly from Lean

## Setup

### Prerequisites

- **Lean 4** / **Lake**: Install via [elan](https://github.com/leanprover/elan)
  ```bash
  curl https://elan-init.lean-lang.org/ -sSf | sh
  ```

- **Z3 SMT Solver**: Required for solving SMT queries
  ```bash
  # macOS
  brew install z3

  # Ubuntu/Debian
  sudo apt-get install z3

  # Or download from https://github.com/Z3Prover/z3/releases
  ```

### Quick Setup

Run the setup script to check and install dependencies:

```bash
./scripts/setup.sh
```

### Build & Run

```bash
lake build
lake exe cogito-core
```

### Run Tests

```bash
lake exe cogito-test
```

### Configuration

| Environment Variable | Description | Default |
|---------------------|-------------|---------|
| `COGITO_Z3_PATH` | Path to Z3 executable | `z3` (uses PATH) |

Example with custom Z3 path:
```bash
COGITO_Z3_PATH=/opt/z3/bin/z3 lake exe cogito-core
```

## Usage

```lean
import CogitoCore

open CogitoCore.SMT

-- Define an SMT query: find x where x + 1 = 10 (8-bit bitvector)
def findX : Smt Unit := do
  let x ← declareBV "x" 8
  assert (x +. bv 1 8 =. bv 10 8)

-- Compile to SMT-LIB2
#eval compile findX
/-
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv10 8)))
-/

-- Solve with Z3 (automatically adds check-sat and get-model)
#eval solve findX
-- Result: sat [(x, #x09)]
```

## Project Structure

```
CogitoCore/
├── SMT/
│   ├── Cmd.lean      -- SMT commands & Smt monad
│   ├── Compile.lean  -- Compile to SMT-LIB2
│   ├── Expr.lean     -- Type-indexed SMT expressions
│   ├── Solver.lean   -- Z3 integration
│   └── Tensor.lean   -- Multi-dimensional tensor support
├── SMT.lean          -- Re-exports SMT modules
Examples/
├── Sudoku.lean       -- 9×9 Sudoku solver
├── NQueens.lean      -- N-Queens puzzle solver
├── Eternity2.lean    -- Eternity II edge-matching puzzle
├── Life.lean         -- Conway's Game of Life verification
└── Minesweeper.lean  -- Minesweeper auto-solver
Main.lean             -- CLI entry point
Tests/
└── SMT.lean          -- Test suite
```

## Examples

### Sudoku Solver
Solves a 9×9 Sudoku puzzle using bitvector constraints.
```bash
lake exe sudoku
```

### N-Queens Puzzle
Places N queens on an N×N chessboard such that no two queens attack each other.
```bash
lake exe nqueens
```

### Eternity II Puzzle
Solves edge-matching puzzles where pieces must be placed so adjacent edges match.
```bash
lake exe eternity2
```

### Conway's Game of Life
Verifies the famous "LIFE" pattern from Knuth's TAOCP using SMT. Given an initial pattern, Z3 confirms it evolves to spell "LIFE" after 3 steps of Conway's Game of Life rules.
```bash
lake exe life
```

### Minesweeper Solver
Automatically solves Minesweeper puzzles by using SMT to deduce which cells are definitely safe or definitely mines. Iteratively reveals safe cells until the entire grid is solved.
```bash
lake exe minesweeper
```

## License

See [LICENSE](LICENSE).
