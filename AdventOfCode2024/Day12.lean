import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day12.txt"

def coords: IO ((h: ℕ) × (w: ℕ) × (Coord h w → Char)) := do
  let lines ← input
  let h := lines.length
  let w := (String.length <$> lines[0]?).getD 0
  if hw: ∀ line ∈ lines, line.length = w then
    return ⟨h, w, fun (y, x) => lines[y].get! ⟨x⟩⟩
  else .error "Uneven line length"

partial def computeRegion (start: Coord h w) (f: Coord h w → Char): Std.HashSet (Coord h w) :=
  --dbg_trace start
  go start {} (f start)
where
  go (pt: Coord h w) soFar ch: Std.HashSet (Coord h w) := Id.run do
    --dbg_trace pt
    let neighbors := pt.neighbors.filter (f · = ch)

    let mut map := soFar.insert pt
    for neighbor in neighbors do
      if neighbor ∉ map then
        map := map ∪ (go neighbor map ch)
    return map

partial def allRegions (start: Coord h w) (f: Coord h w → Char): List (Std.HashSet (Coord h w)) :=
  let initUnvisited := Std.HashSet.insertMany {} (Coord.all h w)
  go start initUnvisited []
where
  go pt (unvisited: Std.HashSet (Coord h w)) acc :=
    let region := computeRegion pt f
    let unvisited' := unvisited.filter (· ∉ region)
    match unvisited'.toList.head? with
    | none => region :: acc
    | some nextPt => go nextPt unvisited' (region :: acc)

def countNeighborsInRegion (region: Std.HashSet (Coord h w)) :=
  region.inner.map fun pt () =>
    let neighborsInRegion := pt.neighbors.countP (· ∈ region)
    have := calc neighborsInRegion
      _ ≤ pt.neighbors.length := List.countP_le_length ..
      _ ≤ 4 := Coord.length_neighbors
      _ < 5 := Nat.lt_succ_self _
    --dbg_trace "{pt} {neighborsInRegion}"
    Fin.mk neighborsInRegion this

def ans₁: IO ℕ := do
  let ⟨h, w, f⟩ ← coords
  if hyp: h > 0 ∧ w > 0 then
    let start := Coord.upperLeft hyp.left hyp.right
    let regions := allRegions start f
    --dbg_trace "{repr regions}"

    let prices := regions.map fun region =>
      let area := region.size
      let perimeter := countNeighborsInRegion region
        |>.values
        |>.map (show ℕ from Fin.sub 4 ·)
        |>.sum
      --dbg_trace "{area} {perimeter} {countNeighborsInRegion region|>.toList}"
      area * perimeter

    return prices.sum
  else .error s!"h = `{h}`, w = `{w}`, but both should be > 0"

/-- number edges = number corners. we count a corner if
    - for any point in the region,
      the (north, east), (east, south), (south, west), or (west, north)
      directions are both not in the set (convex case)
    - for any point *not* in the region, the [...] directions
      are both in the set (concave case)
-/
def countCorners (set: Std.HashSet (Coord h w)): ℕ :=
  let orthogonalPairs := open Coord.Facing in
    [(north, east), (east, south), (south, west), (west, north)]
  set.fold (init := 0) fun acc pt =>
    let ptCorners := List.sum <| orthogonalPairs.map fun (f₁, f₂) =>
      let facing₁ := pt.neighborFacing f₁
      let facing₂ := pt.neighborFacing f₂

      let isConvexCorner := facing₁.all (· ∉ set) && facing₂.all (· ∉ set)
      let isConcaveCorner (_) := Id.run do
        -- other should be a point ∉ set adjacent to
        -- this point and another point in the set
        let some other := facing₁
          | return false
        unless other ∉ set do return false
        let some otherNeighbor := other.neighborFacing f₂
          | return false
        return otherNeighbor ∈ set
      (isConvexCorner || isConcaveCorner ()).toNat
    acc + ptCorners

def ans₂: IO ℕ := do
  let ⟨h, w, f⟩ ← coords
  if hyp: h > 0 ∧ w > 0 then
    let start := Coord.upperLeft hyp.left hyp.right
    let regions := allRegions start f

    let prices := regions.map fun region =>
      let area := region.size
      let corners := countCorners region

      --dbg_trace s!"{corners} {f (region.toList.headD start)} {region.toList}"
      area * corners

    return prices.sum
  else .error s!"h = `{h}`, w = `{w}`, but both should be > 0"
