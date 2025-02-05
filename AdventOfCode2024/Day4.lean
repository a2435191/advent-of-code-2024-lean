import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day4.txt"

structure WordSearch where
  h: ℕ
  w: ℕ
  grid: Coord h w → Char

def wordSearch: IO WordSearch := do
  let lines := (←input).map (·.toList.toArray)|>.toArray
  let h := lines.size
  let w := (Array.size <$> lines[0]?).getD 0
  if hw: lines.all (·.size = w) then
    return { h, w, grid := fun (y, x) =>
      have: Array.size lines[y] = w := by
        have: lines[y] ∈ lines :=
          Array.mem_iff_getElem.mpr ⟨y, y.isLt, rfl⟩
        simp [Array.all_eq_true_iff_forall_mem] at hw
        rwa [hw]
      lines[y][x] }
  else
    .error s!"Uneven line length in `{lines}`"

inductive Direction8
| cardinal: Coord.Facing → Direction8
| intercardinal: Coord.Facing → Coord.Facing → Direction8

instance : ToString Direction8 where
  toString d8 :=
    let ofCardinal: Coord.Facing → String
      | .north => "N"
      | .east  => "E"
      | .south => "S"
      | .west  => "W"
    match d8 with
    | .cardinal c => ofCardinal c
    | .intercardinal c₁ c₂ => ofCardinal c₁ ++ ofCardinal c₂


@[inline]
def Direction8.all: List Direction8 :=
  [.cardinal .north, .cardinal .east, .cardinal .south, .cardinal .west,
   .intercardinal .north .east, .intercardinal .south .east,
   .intercardinal .south .west, .intercardinal .north .west]

@[inline]
def Coord.neighborFacing8 (c: Coord h w): Direction8 → Option (Coord h w )
| .cardinal dir => c.neighborFacing dir
| .intercardinal dir₁ dir₂ => (c.neighborFacing dir₁) >>= (·.neighborFacing dir₂)

/-- Count all the locations in `ws.grid` that align with `pat`, meaning we can line up
    the upper-left corner of `pat` with such a location and all the characters agree. If a coordinate
    is not in the keys of `pat`, then it is treated like a wildcard. -/
def WordSearch.searchPattern (ws: WordSearch) (pat: Std.HashMap (Coord h' w') Char): MLList Id (Coord ws.h ws.w) :=
  (Coord.all ws.h ws.w).filter fun (y, x) =>
    if hyp: ↑y + h' ≤ ws.h ∧ ↑x + w' ≤ ws.w then
      -- search over the sliding window `pat` with the upper-left corner at `(y, x)`
      pat.toList.all fun ((Δy, Δx), patChar) =>
        have hy: ↑y + ↑Δy < ws.h := trans
          (Nat.add_lt_add_iff_left.mpr Δy.isLt)
          hyp.left
        have hx: ↑x + ↑Δx < ws.w := trans
          (Nat.add_lt_add_iff_left.mpr Δx.isLt)
          hyp.right
        let wsChar := ws.grid (⟨y + Δy, hy⟩, ⟨x + Δx, hx⟩)
        patChar = wsChar
   else false -- can't fit the sliding window

/-- For each string in `strings`, count the number of upper-left starting locations that match
    the `coords` mapped (zipped) to the characters in the string. If the same coordinate
    matches multiple patterns, it is counted multiple times. -/
def countCoords (ws: WordSearch) (strings: List String) (coords: List (Coord h w)): ℕ :=
  let map := strings.map fun s =>
      Std.HashMap.ofList <| coords.zip (String.toList s)
    let foundCoords := map.map ws.searchPattern
    (foundCoords.map (β := ℕ) (MLList.length)).sum

def ans₁: IO ℕ := do
  let ws ← wordSearch
  let horiz: List (Coord 1 4) := [(0, 0), (0, 1), (0, 2), (0, 3)]
  let vert : List (Coord 4 1) := [(0, 0), (1, 0), (2, 0), (3, 0)]
  let diag₁: List (Coord 4 4) := [(0, 0), (1, 1), (2, 2), (3, 3)]
  let diag₂: List (Coord 4 4) := [(3, 0), (2, 1), (1, 2), (0, 3)]
  let strings := ["XMAS", "SAMX"]

  let allCoordPatterns: List ((h: ℕ) × (w: ℕ) × List (Coord h w)) := [
    ⟨_, _, horiz⟩, ⟨_, _, vert⟩, ⟨_, _, diag₁⟩, ⟨_, _, diag₂⟩
  ]
  return List.sum <| allCoordPatterns.map
    fun ⟨_, _, coords⟩ => countCoords ws strings coords

#eval ans₁

def ans₂: IO ℕ := do
  let ws ← wordSearch
  let coords: List (Coord 3 3) := [(0, 0), (0, 2), (1, 1), (2, 0), (2, 2)]
  let strings := ["MSAMS", "MMASS", "SSAMM", "SMASM"]

  return countCoords ws strings coords

#eval ans₂
