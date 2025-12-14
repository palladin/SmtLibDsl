# CogitoCore

An experimental project exploring the combination of **dependently-typed Lean DSL for SMT-LIB** with **Z3** and **powerful LLMs** to solve challenging reasoning puzzles and problems.

## The Idea

CogitoCore leverages the strengths of multiple paradigms:

- **Lean 4**: A dependently-typed functional programming language that enables precise, type-safe specifications
- **SMT-LIB / Z3**: Industry-standard satisfiability modulo theories solver for automated reasoning
- **Large Language Models**: AI-powered understanding and problem decomposition

By combining formal verification techniques with modern AI capabilities, CogitoCore aims to tackle complex logical reasoning tasks that neither approach could solve alone.

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
(check-sat)
(get-model)
-/

-- Solve with Z3
#eval solve findX
-- Result: sat [(x, #x09)]
```

## Project Structure

```
CogitoCore/
├── SMT/
│   ├── BitVec.lean   -- Type-indexed BV expressions
│   ├── Cmd.lean      -- SMT commands & Smt monad
│   ├── Compile.lean  -- Compile to SMT-LIB2
│   └── Solver.lean   -- Z3 integration
├── SMT.lean          -- Re-exports
└── CogitoCore.lean   -- Main library
```

## License

See [LICENSE](LICENSE).
