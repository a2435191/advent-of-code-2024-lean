import AdventOfCode2024.Basic

def data := load "AdventOfCode2024/Inputs/Day20.txt"

def countCheatTimeSaves (minTimeSave: ℤ) (maxCheatDistance: ℕ): IO ℕ := do
  let maze ← Maze.parse (←data)
  let edges (p: Coord maze.h maze.w) :=
    p.neighbors
    |>.filter maze.track.contains
    |>.map (·, 1)
    |>.toArray

  let (distStart, _) := dijkstra edges maze.start
  let (distEnd, _) := dijkstra edges maze.end

  let noCheatTime ← match distStart maze.end with
  | some time => pure time
  | none => throw (.userError s!"start {maze.start} has no path to end {maze.end}")

  /- The only legal cheats are those starting and ending on track.
    Additionally, starting a cheat further from the start than
    the optimal no-cheat path length is useless, and similarly for
    the end. -/
  let cheats := maze.track
    |>.filter (fun p => (distStart p).all (· < noCheatTime))
    |>.toArray
    |> MLList.ofArray
    |>.bind (fun p =>
      let qs :=
        Coord.withinTaxicabDist maxCheatDistance p
          |>.filter maze.track.contains
      qs.map (p, ·))
    |>.filter (fun (_, q) =>
      (distEnd q).all (· < noCheatTime))

  let cheatSavedTimes :=
    cheats.map (fun (c₁, c₂) => do
      let cheatDistance := Coord.taxicabDist c₁ c₂

      let distTo_c₁ := distStart c₁
      let distFrom_c₂ := distEnd c₂

      let cheatTime := (Nat.add · · + cheatDistance) <$> distTo_c₁ <*> distFrom_c₂
      let timeSaved := Int.sub noCheatTime <$> cheatTime
      timeSaved)

  return cheatSavedTimes
    |>.filterMap (Option.filter (· ≥ minTimeSave))
    |>.length

def ans₁: IO Nat :=
  countCheatTimeSaves 100 2

def ans₂: IO Nat :=
  countCheatTimeSaves 100 20
