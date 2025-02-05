import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day6.txt"

structure Guard (h w: ℕ) where
  pos: Coord h w
  facing: Coord.Facing
deriving Repr, BEq, Hashable

inductive TileType
| guard (facing: Coord.Facing)
| obstacle
| empty
deriving DecidableEq, Hashable

def parseLab: IO ((h: ℕ) × (w: ℕ) × Std.HashSet (Coord h w) × Guard h w) := do
  let lines ← input
  let h := lines.length
  let w := (String.length <$> lines.head?).getD 0

  if hw: ∀ line ∈ lines, line.length = w then
    let grid ← Grid.parse lines rfl hw fun coord c =>
      match c with
      | '.' => some (coord, TileType.empty)
      | '#' => some (coord, .obstacle)
      | '^' => some (coord, .guard .north)
      | '<' => some (coord, .guard .west)
      | 'v' => some (coord, .guard .south)
      | '>' => some (coord, .guard .east)
      | _ => none

    let obstacles := Std.HashSet.ofList <| grid.filterMap fun
      | (coord, .obstacle) => some coord
      | _ => none

    let guards := grid.filterMap fun
        | (coord, .guard facing) => some (coord, facing)
        | _ => none
    let [(pos, facing)] := guards | .error s!"Not exactly one guard: `{repr guards}`"
    return ⟨h, w, obstacles, { pos, facing }⟩
  else .error s!"Uneven line length in `{lines}`"

def next (obstacles: Std.HashSet (Coord h w)): Guard h w → Option (Guard h w)
| { pos, facing } => do
  let nextPos ← pos.neighborFacing facing
  if nextPos ∈ obstacles then
    let nextFacing := match facing with
      | .north => .east
      | .west => .north
      | .south => .west
      | .east => .south
    return { pos, facing := nextFacing }
  return { pos := nextPos, facing }

/-- `none` if the guard loops forever, `some n` otherwise,
    where `n` is the number of unique positions they visit -/
partial def simulate (obstacles: Std.HashSet (Coord h w)) (guardInit: Guard h w): Option ℕ :=
  let rec aux (guard: Guard h w) (visited: Std.HashSet (Guard h w)): Option ℕ :=
    match next obstacles guard with
    | some guard' =>
      if guard' ∈ visited then
        none
      else
        aux guard' (visited.insert guard')
    | none =>
      let coordsVisited: Std.HashSet (Coord h w) := visited.fold (init := {})
        fun acc guard => acc.insert guard.pos
      some coordsVisited.size

  aux guardInit { guardInit }

def ans₁ := do
  let ⟨_, _, obstacles, guard⟩ ← parseLab
  let some numCoordsVisited := simulate obstacles guard
    | .error "ans₁ got `none`"
  return numCoordsVisited

def ans₂ := do
  let ⟨h, w, obstacles, guard⟩ ← parseLab
  return Coord.all h w
    |>.filter (fun obstruction =>
      obstruction ∉ obstacles
      && (simulate (obstacles.insert obstruction) guard).isNone)
    |>.length

-- #eval ans₂
