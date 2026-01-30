/-
  SmtLibDsl - SMT-LIB BitVector Theory DSL
  Z3 solver integration
-/
import SmtLibDsl.SMT.Compile

namespace SmtLibDsl.SMT

/-- Model holding variable assignments, indexed by schema -/
structure Model (vars : VarSchema) where
  raw : List (String × String)

/-- Lookup a variable value by name (runtime check, raw string) -/
def Model.lookup (m : Model vars) (name : String) : Option String :=
  m.raw.lookup name

/-- Get a variable value with proof it exists in schema, parsed to Lean type -/
def Model.get (m : Model vars) (name : String) (ty : Ty)
    (_h : (name, ty) ∈ vars := by decide) : Option ty.LeanType :=
  m.raw.lookup name >>= ty.parse

instance : ToString (Model vars) where
  toString m := toString m.raw

/-- Result of a satisfiability check, indexed by variable schema -/
inductive Result (vars : VarSchema) where
  | sat (model : Model vars)
  | unsat
  | unknown (reason : String)

instance : ToString (Result vars) where
  toString
  | .sat model => s!"sat\n{model}"
  | .unsat => "unsat"
  | .unknown reason => s!"unknown ({reason})"

/-- Parse the output from Z3 -/
private def parseResultRaw (output : String) : (List (String × String)) ⊕ String :=
  let lines := output.splitOn "\n" |>.filter (·.length > 0)
  match lines with
  | "sat" :: rest => .inl (parseModel (String.intercalate " " rest))
  | "unsat" :: _ => .inr "unsat"
  | "unknown" :: rest => .inr s!"unknown: {String.intercalate " " rest}"
  | _ => .inr s!"Failed to parse: {output}"
where
  parseModel (modelStr : String) : List (String × String) :=
    -- Parse: (define-fun name () Type value)
    -- Join all lines and extract define-fun blocks
    let s := modelStr.replace "\n" " " |>.replace "  " " "
    extractDefineFuns s []
  extractDefineFuns (s : String) (acc : List (String × String)) : List (String × String) :=
    match s.splitOn "(define-fun " with
    | [] => acc.reverse
    | _ :: rest =>
      let pairs := rest.filterMap fun part =>
        -- part looks like: "x () (_ BitVec 8) #x09) ..."
        let tokens := part.splitOn " " |>.filter (·.length > 0)
        match tokens with
        | name :: "()" :: _ =>
          -- Find the value: after the type, before the closing paren
          -- Look for #x... or #b... or a number
          let valueOpt := tokens.find? fun t =>
            t.startsWith "#x" || t.startsWith "#b" || t.all Char.isDigit
          match valueOpt with
          | some v => some (name, v.dropRightWhile (· == ')'))
          | none =>
            -- Try to find "true" or "false" for booleans
            if tokens.contains "true" then some (name, "true")
            else if tokens.contains "false" then some (name, "false")
            else none
        | _ => none
      acc.reverse ++ pairs

/-- Configuration for the solve function -/
structure SolveConfig where
  /-- Dump the generated SMT-LIB2 script to stdout -/
  dumpSmt : Bool := false
  /-- Optional timeout in milliseconds for Z3 -/
  timeout : Option Nat := none
  /-- Dump profiling info (compile time, Z3 solve time) -/
  profile : Bool := false

instance : Inhabited SolveConfig where
  default := {}

/-- Get the Z3 executable path from environment or default -/
def getZ3Path : IO String := do
  match ← IO.getEnv "SMTLIBDSL_Z3_PATH" with
  | some path => pure path
  | none => pure "z3"

/-- Check if Z3 is available -/
def checkZ3 : IO (Except String String) := do
  let z3Path ← getZ3Path
  try
    let result ← IO.Process.output {
      cmd := z3Path
      args := #["--version"]
    }
    if result.exitCode == 0 then
      return .ok result.stdout.trim
    else
      return .error s!"Z3 returned error: {result.stderr}"
  catch _ =>
    return .error s!"Z3 not found at '{z3Path}'.\n\nInstall Z3:\n  • macOS:  brew install z3\n  • Ubuntu: sudo apt-get install z3\n  • Or set SMTLIBDSL_Z3_PATH environment variable"

/-- Run Z3 on an SMT-LIB2 script string -/
def runZ3 (vars : VarSchema) (script : String) (timeout : Option Nat := none) (profile : Bool := false) : IO (Result vars) := do
  let z3Path ← getZ3Path
  let tempFile := "/tmp/smtlibdsl_query.smt2"
  IO.FS.writeFile tempFile script
  if profile then
    let sizeBytes := script.utf8ByteSize
    let sizeKb := sizeBytes.toFloat / 1024.0
    IO.println s!"  SMT file size: {sizeBytes} bytes ({sizeKb.toString}KB)"
  try
    let timeoutArgs := match timeout with
      | some ms => #[s!"-t:{ms}"]
      | none => #[]
    let output ← IO.Process.output {
      cmd := z3Path
      args := timeoutArgs ++ #["-smt2", tempFile]
    }
    if output.exitCode != 0 && output.exitCode != 1 then
      return .unknown s!"Z3 error: {output.stderr}"
    match parseResultRaw output.stdout with
    | .inl model => return .sat ⟨model⟩
    | .inr "unsat" => return .unsat
    | .inr reason =>
      -- Detect timeout: Z3 returns "unknown" and model is not available
      if (reason.splitOn "model is not available").length > 1 then
        match timeout with
        | some ms => return .unknown s!"timeout ({ms}ms)"
        | none => return .unknown "timeout"
      else
        return .unknown reason
  catch e =>
    return .unknown s!"Failed to run Z3: {e}\n\nInstall Z3:\n  • macOS:  brew install z3\n  • Ubuntu: sudo apt-get install z3\n  • Or set SMTLIBDSL_Z3_PATH environment variable"

/-- Compile and solve an Smt program using Z3, returning schema-indexed result -/
def solve (smt : Smt Unit) (config : SolveConfig := {}) : IO (Result smt.schema) := do
  -- Compile to SMT-LIB2
  let compileStart ← IO.monoNanosNow
  let script := compile smt
  let compileEnd ← IO.monoNanosNow
  let compileTimeMs := (compileEnd - compileStart).toFloat / 1_000_000.0

  if config.dumpSmt then
    IO.println "SMT-LIB2 Script:"
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println script
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println ""

  -- Run Z3
  let z3Start ← IO.monoNanosNow
  let result ← runZ3 smt.schema script config.timeout config.profile
  let z3End ← IO.monoNanosNow
  let z3TimeMs := (z3End - z3Start).toFloat / 1_000_000.0

  if config.profile then
    IO.println "Profile:"
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println s!"  Compile time: {compileTimeMs.toString}ms"
    IO.println s!"  Z3 solve time: {z3TimeMs.toString}ms"
    IO.println s!"  Total time: {(compileTimeMs + z3TimeMs).toString}ms"
    IO.println (String.mk (List.replicate 40 '─'))
    IO.println ""

  return result

/-- Print the compiled SMT-LIB2 script (for debugging) -/
def printScript (smt : Smt Unit) : IO Unit := do
  IO.println (compile smt)

end SmtLibDsl.SMT
