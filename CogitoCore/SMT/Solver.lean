/-
  CogitoCore - SMT-LIB BitVector Theory DSL
  Z3 solver integration
-/
import CogitoCore.SMT.Compile

namespace CogitoCore.SMT

/-- Result of a satisfiability check -/
inductive Result where
  | sat (model : List (String × String))
  | unsat
  | unknown (reason : String)
deriving Repr

instance : ToString Result where
  toString
  | .sat model => s!"sat\n{model}"
  | .unsat => "unsat"
  | .unknown reason => s!"unknown ({reason})"

/-- Parse the output from Z3 -/
private def parseResult (output : String) : Result :=
  let lines := output.splitOn "\n" |>.filter (·.length > 0)
  match lines with
  | "sat" :: rest => .sat (parseModel (String.intercalate " " rest))
  | "unsat" :: _ => .unsat
  | "unknown" :: rest => .unknown (String.intercalate " " rest)
  | _ => .unknown s!"Failed to parse: {output}"
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

/-- Get the Z3 executable path from environment or default -/
def getZ3Path : IO String := do
  match ← IO.getEnv "COGITO_Z3_PATH" with
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
    return .error s!"Z3 not found at '{z3Path}'.\n\nInstall Z3:\n  • macOS:  brew install z3\n  • Ubuntu: sudo apt-get install z3\n  • Or set COGITO_Z3_PATH environment variable"

/-- Run Z3 on an SMT-LIB2 script string -/
def runZ3 (script : String) : IO Result := do
  let z3Path ← getZ3Path
  let tempFile := "/tmp/cogito_query.smt2"
  IO.FS.writeFile tempFile script
  try
    let output ← IO.Process.output {
      cmd := z3Path
      args := #["-smt2", tempFile]
    }
    if output.exitCode != 0 && output.exitCode != 1 then
      return .unknown s!"Z3 error: {output.stderr}"
    return parseResult output.stdout
  catch e =>
    return .unknown s!"Failed to run Z3: {e}\n\nInstall Z3:\n  • macOS:  brew install z3\n  • Ubuntu: sudo apt-get install z3\n  • Or set COGITO_Z3_PATH environment variable"

/-- Compile and solve an Smt program using Z3 -/
def solve (smt : Smt Unit) : IO Result := do
  let script := compile smt ++ "\n(check-sat)\n(get-model)"
  runZ3 script

/-- Print the compiled SMT-LIB2 script (for debugging) -/
def printScript (smt : Smt Unit) : IO Unit := do
  IO.println (compile smt)

end CogitoCore.SMT
