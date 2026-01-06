/-
  CogitoCore - Sokoban Puzzle SMT Solver

  Sokoban is a classic puzzle game where you push boxes onto goal positions.
  Rules:
  - Player can move up/down/left/right into empty spaces
  - Player can push a box if the space behind the box is empty
  - Boxes cannot be pushed into walls or other boxes
  - Goal: get all boxes onto target positions

  This solver uses SMT to find a sequence of moves that solves the puzzle.
  State at each step: player position + all box positions
  We iteratively increase the maximum steps until a solution is found.
-/
import CogitoCore
import Examples.SokobanLevels

open CogitoCore.SMT

namespace Sokoban

/-! ## Configuration -/

/-- Bit width for coordinates (8-bit is enough for reasonable grids) -/
abbrev W : Nat := 8

/-- Type alias for coordinate expressions -/
abbrev Coord := Expr (Ty.bitVec W)

/-- Direction encoding: 0=Up, 1=Down, 2=Left, 3=Right -/
abbrev Dir := Expr (Ty.bitVec W)

/-! ## Puzzle Definition -/

/-- Cell types in Sokoban -/
inductive Cell where
  | wall    -- # - impassable
  | floor   -- . - empty floor
  | goal    -- * - target position for box
  | player  -- @ - initial player position
  | box     -- $ - box to push
  | boxOnGoal -- + - box already on goal
  | playerOnGoal -- & - player on goal
deriving Repr, BEq

/-- Parse a character to a cell -/
def Cell.fromChar : Char → Cell
  | '#' => .wall
  | ' ' => .floor
  | '.' => .goal
  | '*' => .boxOnGoal
  | '@' => .player
  | '$' => .box
  | '+' => .playerOnGoal
  | _   => .floor

/-- Convert cell to display character -/
def Cell.toChar : Cell → Char
  | .wall => '#'
  | .floor => ' '
  | .goal => '·'
  | .player => '@'
  | .box => '$'
  | .boxOnGoal => '✓'
  | .playerOnGoal => '@'

/-- A Sokoban level -/
structure Level where
  width : Nat
  height : Nat
  walls : List (Nat × Nat)      -- Wall positions
  goals : List (Nat × Nat)      -- Target positions
  initialPlayer : Nat × Nat     -- Starting player position
  initialBoxes : List (Nat × Nat) -- Starting box positions
  deadCorners : List (Nat × Nat) -- Corner positions that are not goals (deadlock if box placed)
deriving Repr

/-- Check if a position is a wall in the raw grid -/
def isWallAt (walls : List (Nat × Nat)) (r c : Nat) : Bool :=
  walls.any fun (wr, wc) => wr == r && wc == c

/-- Check if a position is a goal -/
def isGoalAt (goals : List (Nat × Nat)) (r c : Nat) : Bool :=
  goals.any fun (gr, gc) => gr == r && gc == c

/-- Compute dead corners: floor cells with walls on two adjacent sides, not goals -/
def computeDeadCorners (width height : Nat) (walls goals : List (Nat × Nat)) : List (Nat × Nat) := Id.run do
  let mut corners : List (Nat × Nat) := []
  for r in List.range height do
    for c in List.range width do
      -- Skip if wall or goal
      if isWallAt walls r c || isGoalAt goals r c then
        continue
      -- Check for corner patterns (walls on two adjacent sides)
      let wallUp := r == 0 || isWallAt walls (r - 1) c
      let wallDown := isWallAt walls (r + 1) c
      let wallLeft := c == 0 || isWallAt walls r (c - 1)
      let wallRight := isWallAt walls r (c + 1)
      -- Corner if blocked in two perpendicular directions
      let isCorner := (wallUp && wallLeft) || (wallUp && wallRight) ||
                      (wallDown && wallLeft) || (wallDown && wallRight)
      if isCorner then
        corners := (r, c) :: corners
  corners

/-- Parse a level from string lines -/
def Level.parse (lines : List String) : Level := Id.run do
  let height := lines.length
  let width := lines.foldl (fun acc l => max acc l.length) 0

  let mut walls : List (Nat × Nat) := []
  let mut goals : List (Nat × Nat) := []
  let mut boxes : List (Nat × Nat) := []
  let mut player : Nat × Nat := (0, 0)

  for row in List.range height do
    match lines[row]? with
    | some line =>
      for col in List.range line.length do
        match line.get? ⟨col⟩ with
        | some c =>
          match Cell.fromChar c with
          | .wall => walls := (row, col) :: walls
          | .goal => goals := (row, col) :: goals
          | .player => player := (row, col)
          | .box => boxes := (row, col) :: boxes
          | .boxOnGoal =>
            goals := (row, col) :: goals
            boxes := (row, col) :: boxes
          | .playerOnGoal =>
            goals := (row, col) :: goals
            player := (row, col)
          | _ => pure ()
        | none => pure ()
    | none => pure ()

  { width, height, walls, goals, initialPlayer := player, initialBoxes := boxes,
    deadCorners := computeDeadCorners width height walls goals }

/-! ## SMT Helpers -/

/-- Create a coordinate literal -/
def coord (n : Nat) : Coord := bv n W

/-- Direction constants -/
def dirUp : Dir := coord 0
def dirDown : Dir := coord 1
def dirLeft : Dir := coord 2
def dirRight : Dir := coord 3

/-- Check if position is a wall -/
def isWall (level : Level) (r c : Coord) : Expr Ty.bool :=
  level.walls.foldl (fun acc (wr, wc) =>
    acc ∨. ((r =. coord wr) ∧. (c =. coord wc))) Expr.bfalse

/-- Check if position is a dead corner (box here = deadlock) -/
def isDeadCorner (level : Level) (r c : Coord) : Expr Ty.bool :=
  level.deadCorners.foldl (fun acc (cr, cc) =>
    acc ∨. ((r =. coord cr) ∧. (c =. coord cc))) Expr.bfalse

/-- Compute new position after moving in direction -/
def movePos (r c dir : Coord) : (Coord × Coord) :=
  let newR := Expr.ite (dir =. dirUp) (r -. coord 1)
             (Expr.ite (dir =. dirDown) (r +. coord 1) r)
  let newC := Expr.ite (dir =. dirLeft) (c -. coord 1)
             (Expr.ite (dir =. dirRight) (c +. coord 1) c)
  (newR, newC)

/-! ## State Representation -/

/-- State at a given timestep -/
structure State where
  playerRow : Coord
  playerCol : Coord
  boxRows : List Coord
  boxCols : List Coord

/-- Declare state variables for a timestep -/
def declState (tag : String) (numBoxes : Nat) : Smt State := do
  let playerRow ← declareBV s!"{tag}_pr" W
  let playerCol ← declareBV s!"{tag}_pc" W
  let mut boxRows : List Coord := []
  let mut boxCols : List Coord := []
  for i in List.range numBoxes do
    let br ← declareBV s!"{tag}_br_{i}" W
    let bc ← declareBV s!"{tag}_bc_{i}" W
    boxRows := boxRows ++ [br]
    boxCols := boxCols ++ [bc]
  pure { playerRow, playerCol, boxRows, boxCols }

/-- Assert initial state matches level -/
def assertInitialState (state : State) (level : Level) : Smt Unit := do
  let (pr, pc) := level.initialPlayer
  assert (state.playerRow =. coord pr)
  assert (state.playerCol =. coord pc)
  for i in List.range level.initialBoxes.length do
    match level.initialBoxes[i]?, state.boxRows[i]?, state.boxCols[i]? with
    | some (br, bc), some boxR, some boxC =>
      assert (boxR =. coord br)
      assert (boxC =. coord bc)
    | _, _, _ => pure ()

/-- Check if position matches any box -/
def isBox (state : State) (r c : Coord) : Expr Ty.bool :=
  (state.boxRows.zip state.boxCols).foldl (fun acc (br, bc) =>
    acc ∨. ((r =. br) ∧. (c =. bc))) Expr.bfalse

/-- Assert goal state: all boxes on goals -/
def assertGoalState (state : State) (level : Level) : Smt Unit := do
  -- Each box must be on some goal
  for (boxR, boxC) in state.boxRows.zip state.boxCols do
    let onGoal := level.goals.foldl (fun acc (gr, gc) =>
      acc ∨. ((boxR =. coord gr) ∧. (boxC =. coord gc))) Expr.bfalse
    assert onGoal

/-- Assert no box is in a dead corner (early deadlock detection) -/
def assertNoDeadlock (state : State) (level : Level) : Smt Unit := do
  -- If no dead corners, skip
  if level.deadCorners.isEmpty then return
  -- Each box must NOT be in a dead corner
  for (boxR, boxC) in state.boxRows.zip state.boxCols do
    let inDeadCorner := isDeadCorner level boxR boxC
    assert (¬. inDeadCorner)

/-! ## Transition Constraints -/

/-- Assert valid transition from state to nextState via direction -/
def assertTransition (level : Level) (state nextState : State) (dir : Dir) : Smt Unit := do
  -- Compute player's target position
  let (targetR, targetC) := movePos state.playerRow state.playerCol dir

  -- Is target a wall?
  let targetIsWall := isWall level targetR targetC

  -- Is target a box?
  let targetIsBox := isBox state targetR targetC

  -- Position behind the box (if pushing)
  let (behindR, behindC) := movePos targetR targetC dir
  let behindIsWall := isWall level behindR behindC
  let behindIsBox := isBox state behindR behindC

  -- Valid move: target is not a wall
  -- If target is a box, behind must be free (not wall, not box)
  let canPush := ¬. behindIsWall ∧. ¬. behindIsBox
  let validMove := ¬. targetIsWall ∧. (¬. targetIsBox ∨. canPush)
  assert validMove

  -- Player moves to target
  assert (nextState.playerRow =. Expr.ite validMove targetR state.playerRow)
  assert (nextState.playerCol =. Expr.ite validMove targetC state.playerCol)

  -- Update box positions
  let boxes := state.boxRows.zip state.boxCols
  let nextBoxes := nextState.boxRows.zip nextState.boxCols
  for i in List.range boxes.length do
    match boxes[i]?, nextBoxes[i]? with
    | some (boxR, boxC), some (nextBoxR, nextBoxC) =>
      -- This box is pushed if it's at target position
      let thisBoxPushed := (boxR =. targetR) ∧. (boxC =. targetC) ∧. targetIsBox ∧. canPush
      -- If pushed, move in direction; otherwise stay
      let (pushedR, pushedC) := movePos boxR boxC dir
      assert (nextBoxR =. Expr.ite thisBoxPushed pushedR boxR)
      assert (nextBoxC =. Expr.ite thisBoxPushed pushedC boxC)
    | _, _ => pure ()

/-! ## Main Solver -/

/-- Build SMT problem for solving Sokoban in at most n steps -/
def sokoban (level : Level) (maxSteps : Nat) : Smt (List Dir) := do
  let numBoxes := level.initialBoxes.length

  -- Declare states for each timestep
  let mut states : List State := []
  for t in List.range (maxSteps + 1) do
    let state ← declState s!"s{t}" numBoxes
    states := states ++ [state]

  -- Declare direction for each step
  let mut dirs : List Dir := []
  for t in List.range maxSteps do
    let dir ← declareBV s!"dir_{t}" W
    -- Valid direction: 0, 1, 2, or 3
    assert ((dir =. dirUp) ∨. (dir =. dirDown) ∨. (dir =. dirLeft) ∨. (dir =. dirRight))
    dirs := dirs ++ [dir]

  -- Assert initial state
  match states.head? with
  | some s0 => assertInitialState s0 level
  | none => pure ()

  -- Assert transitions and deadlock constraints for each timestep
  for t in List.range dirs.length do
    match states[t]?, states[t + 1]?, dirs[t]? with
    | some st, some st', some dir =>
      assertTransition level st st' dir
      -- No deadlock at the next state (prune dead ends early!)
      assertNoDeadlock st' level
    | _, _, _ => pure ()

  -- Assert goal state at final state
  match states.getLast? with
  | some sf => assertGoalState sf level
  | none => pure ()

  pure dirs

/-- Wrapper for solving -/
def sokobanQuery (level : Level) (maxSteps : Nat) : Smt Unit := do
  let _ ← sokoban level maxSteps
  pure ()

/-! ## Display -/

/-- Direction to string -/
def dirToString : Nat → String
  | 0 => "↑"
  | 1 => "↓"
  | 2 => "←"
  | 3 => "→"
  | _ => "?"

/-- Direction to name -/
def dirToName : Nat → String
  | 0 => "Up"
  | 1 => "Down"
  | 2 => "Left"
  | 3 => "Right"
  | _ => "?"

/-- Parse direction from model -/
def parseDir (s : String) : Option Nat :=
  if s.startsWith "#x" then
    let hex := s.drop 2
    hex.foldl (fun acc c =>
      acc.bind fun a =>
        if '0' ≤ c ∧ c ≤ '9' then some (a * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c ∧ c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10))
        else if 'A' ≤ c ∧ c ≤ 'F' then some (a * 16 + (c.toNat - 'A'.toNat + 10))
        else none
    ) (some 0)
  else
    s.toNat?

/-- Extract solution moves from model -/
def extractMoves (model : Model schema) (maxSteps : Nat) : List Nat :=
  List.range maxSteps |>.filterMap fun t =>
    model.lookup s!"dir_{t}" >>= parseDir

/-- Check if position is in list -/
def posInList (pos : Nat × Nat) (lst : List (Nat × Nat)) : Bool :=
  lst.any (· == pos)

/-- Display level with given player and box positions -/
def displayLevel (level : Level) (playerPos : Nat × Nat) (boxes : List (Nat × Nat)) : IO Unit := do
  for r in List.range level.height do
    let mut rowStr := ""
    for c in List.range level.width do
      let pos := (r, c)
      let ch :=
        if pos == playerPos then
          if posInList pos level.goals then '&' else '@'
        else if posInList pos boxes then
          if posInList pos level.goals then '✓' else '$'
        else if posInList pos level.walls then '#'
        else if posInList pos level.goals then '·'
        else ' '
      rowStr := rowStr ++ String.mk [ch]
    IO.println rowStr

end Sokoban

/-! ## Main Entry Point -/

open Sokoban in
def main (args : List String) : IO UInt32 := do
  let dumpSmt := args.contains "--dump-smt" || args.contains "-d"
  let profile := args.contains "--profile" || args.contains "-p"
  let listLevels := args.contains "--list" || args.contains "-l"

  -- Parse level number and optional max steps from args
  let nums := args.filterMap String.toNat?
  let levelNum := nums.head? |>.getD 2
  let maxTries := nums[1]? |>.getD 50  -- Default to 50 max steps

  IO.println "╔═══════════════════════════════════════╗"
  IO.println "║     Sokoban Puzzle SMT Solver         ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println ""

  -- List levels if requested
  if listLevels then
    IO.println "Available levels:"
    IO.println ""
    for i in List.range Levels.levelCount do
      match Levels.allLevels[i]? with
      | some lvl => IO.println s!"  {i + 1}. {lvl.name}"
      | none => pure ()
    IO.println ""
    IO.println "Usage: lake exe sokoban <level_number>"
    IO.println "       lake exe sokoban --list"
    return 0

  -- Check Z3 availability
  match ← CogitoCore.SMT.checkZ3 with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok version =>
    IO.println s!"Using {version}"
    IO.println ""

  -- Get selected level
  let some levelData := Levels.getLevel levelNum
    | do
      IO.eprintln s!"Level {levelNum} not found. Use --list to see available levels."
      return 1

  let level := Level.parse levelData.lines

  IO.println s!"{levelData.name}:"
  displayLevel level level.initialPlayer level.initialBoxes
  IO.println ""
  IO.println s!"Boxes: {level.initialBoxes.length}"
  IO.println s!"Goals: {level.goals.length}"
  IO.println s!"Dead corners: {level.deadCorners.length} (pruning enabled)"
  IO.println s!"Max steps: {maxTries}"
  IO.println ""

  -- Try with increasing number of steps
  for numSteps in List.range maxTries do
    let n := numSteps + 1
    IO.print s!"Trying {n} step(s)... "

    let problem := sokobanQuery level n
    let result ← CogitoCore.SMT.solve problem { dumpSmt := dumpSmt, profile := profile }

    match result with
    | .sat model =>
      IO.println "SAT!"
      IO.println ""
      IO.println s!"✓ Solution found in {n} moves!"
      IO.println ""

      let moves := extractMoves model n
      let moveStrs := moves.map dirToString
      let moveNames := moves.map dirToName
      IO.println s!"Moves: {String.intercalate " " moveStrs}"
      IO.println s!"       ({String.intercalate ", " moveNames})"
      IO.println ""

      -- Animate solution
      IO.println "Solution replay:"
      IO.println "─────────────────"
      let mut playerPos := level.initialPlayer
      let mut boxes := level.initialBoxes

      IO.println "Initial:"
      displayLevel level playerPos boxes
      IO.println ""

      for step in List.range moves.length do
        match moves[step]? with
        | some dir =>
          -- Apply move
          let (pr, pc) := playerPos
          let (dr, dc) : Int × Int := match dir with
            | 0 => (-1, 0)   -- Up
            | 1 => (1, 0)    -- Down
            | 2 => (0, -1)   -- Left
            | 3 => (0, 1)    -- Right
            | _ => (0, 0)
          let targetPos := ((pr : Int) + dr |>.toNat, (pc : Int) + dc |>.toNat)

          -- Check if pushing a box
          if posInList targetPos boxes then
            let behindPos := ((pr : Int) + 2*dr |>.toNat, (pc : Int) + 2*dc |>.toNat)
            boxes := boxes.map fun b => if b == targetPos then behindPos else b

          playerPos := targetPos

          IO.println s!"Move {step + 1}: {dirToString dir}"
          displayLevel level playerPos boxes
          IO.println ""
        | none => pure ()

      IO.println "✓ Puzzle solved!"
      return 0

    | .unsat =>
      IO.println "No solution"
    | .unknown reason =>
      IO.println s!"Unknown: {reason}"

  IO.println ""
  IO.println s!"No solution found within {maxTries} moves."
  return 1
