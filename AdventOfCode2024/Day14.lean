import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day14.txt"

def toFins: List ℕ → (n: ℕ) × List (Fin n)
| [] => ⟨0, []⟩
| x :: xs =>
  match toFins xs with
  | ⟨n, rest⟩ =>
    if hx: x < n then
      ⟨n, ⟨x, hx⟩ :: rest⟩
    else
      have: n ≤ x + 1 := calc
        _ ≤ x := Nat.le_of_not_lt hx
        _ ≤ x + 1 := Nat.le_succ _
      ⟨x + 1, ⟨x, Nat.lt_add_one _⟩ :: rest.map (Fin.castLE this)⟩

def positionsAndVelocities: IO ((w: ℕ) × (h: ℕ) × List (Coord w h × (ℤ × ℤ))) := do
  let lst ← (←input).mapM (fun line => do
    let [xStr, yStr, vStr, uStr] := line
      |>.split (fun c => c ∈ ['p', ',', ' ', 'v', '='])
      |>.filter (not ∘ String.isEmpty)
      | .error s!"Failed to parse line: `{line}` `{line.split (fun c => c ∈ ['p', ',', ' ', 'v', '='])}`"
    return (←xStr.toNat?', ←yStr.toNat?', ←vStr.toInt?', ←uStr.toInt?'))

  let (xs, ys, velocities) := lst.unzip.map id List.unzip
  let ⟨w, xs'⟩ := toFins xs
  let ⟨h, ys'⟩ := toFins ys

  return ⟨w, h, xs'.zip ys'|>.zip velocities⟩

def next {w h} (c: Coord w h) (vx: ℤ) (vy: ℤ) (seconds: ℕ): Coord w h :=
  let (⟨x, hx⟩, ⟨y, hy⟩) := c
  let vx' := Int.natMod vx w
  let vy' := Int.natMod vy h
  let x' := (x + vx' * seconds) % w
  let y' := (y + vy' * seconds) % h
  have hx': x' < w := by simp only [x', Nat.mod_lt, Nat.zero_lt_of_lt hx]
  have hy': y' < h := by simp only [y', Nat.mod_lt, Nat.zero_lt_of_lt hy]
  (⟨x', hx'⟩, ⟨y', hy'⟩)

def ans₁: IO ℕ := do
  let ⟨w, h, data⟩ ← positionsAndVelocities
  let seconds := 100
  let positions: List (Coord w h) := data.map fun (c, vx, vy) => next c vx vy seconds

  let (q₁, q₂, q₃, q₄) := positions
    |>.foldr (init := (0, 0, 0, 0)) fun (⟨x, _⟩, ⟨y, _⟩) (a, b, c, d) =>
      match compare (2 * x + 1) w, compare (2 * y + 1) h with
      | .lt, .lt => (a + 1, b, c, d)
      | .lt, .gt => (a, b + 1, c, d)
      | .gt, .lt => (a, b, c + 1, d)
      | .gt, .gt => (a, b, c, d + 1)
      | _, _     => (a, b, c, d)

  return q₁ * q₂ * q₃ * q₄

#eval ans₁

def display {w h} (robots: List (Coord w h)): String :=
  let set := Std.HashSet.ofList (robots.map fun (⟨x, _⟩, ⟨y, _⟩) => (x, y))
  String.intercalate "\n" <| (List.range h).map fun y =>
    String.mk <| (List.range w).map fun x =>
      if (x, y) ∈ set then '#' else '.'

def List.longestTrueSubseq: List Bool → ℕ :=
  go 0 0
where
  go maxSoFar curLength: List Bool → ℕ
  | [] => max maxSoFar curLength
  | true :: rest =>
    go (max maxSoFar (curLength + 1)) (curLength + 1) rest
  | false :: rest => go maxSoFar 0 rest

def longestContiguousRow (robots: List (Coord w h)): ℕ :=
  let set := Std.HashSet.ofList (robots.map fun (⟨x, _⟩, ⟨y, _⟩) => (x, y))
  List.range h
    |>.map (fun y =>
      List.range w
        |>.map (fun x => set.contains (x, y))
        |>.longestTrueSubseq)
    |>.max?
    |>.getD 0

/--
  Each robot eventually repeats its pattern, taking `lcm(lcm(w, vx) / vx, lcm(h, vy) / vy)` cycles to
  do so. When the dimensions `(w, h)` are prime and `vx < w` and `vy < h` (wrapping negative velocities to positive
  as needed, which we do in `next`), this becomes just `w * h`. Therefore, we only have to search `101 * 103` many
  inputs. (I already found the solution by observing that after time `18 + 101s` and `76 + 103t` large block shapes are formed,
  and then solving for the times that satisfy both for `s, t ∈ ℤ`. This is perhaps a more robust method.) -/
def ans₂: IO ℕ := do
  let ⟨w, h, data⟩ ← positionsAndVelocities
  let (initCoords, velocities) := data.unzip

  -- return largest horizontal streak of filled in coordinates
  let (_, optionResult) := List.range (w * h)
    |>.foldl (init := (initCoords, none)) fun (coords, acc) idx =>
      let coords' := List.zipWith (fun c (vx, vy) => next c vx vy 1) coords velocities
      let score := longestContiguousRow coords'
      let result := match acc with
      | none => (score, idx, coords')
      | some (maxScoreSoFar, bestIdxSoFar, bestCoordsSoFar) =>
        if score > maxScoreSoFar then
          (score, idx, coords')
        else
          (maxScoreSoFar, bestIdxSoFar, bestCoordsSoFar)

      (coords', some result)

  let some (bestScore, bestIdx, bestCoords) := optionResult | .error "Empty list"
  println! bestScore
  println! (display bestCoords)
  return bestIdx + 1 -- + 1 since we start at 0, which is really *after* 1 second
