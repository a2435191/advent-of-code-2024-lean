import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day10.txt"

abbrev Grid h w :=
  Vector (Vector (Fin 10) w) h

def grid: IO ((h: ℕ) × (w: ℕ) × Grid h w) := do
  let lines ← input
  let w := (String.length <$> lines.head?).getD 0

  let lst ← lines.mapM fun line =>
    line.toList.mapM (liftM ∘ Char.toNat?)

  if hyp: ∀ line ∈ lst, line.length = w then
    let vec := lst.attach.toArray.map fun ⟨row, hrow⟩ =>
      Vector.mk row.toArray
        (Array.size_toArray _ ▸ hyp row hrow)
    return ⟨vec.size, w, ⟨vec, rfl⟩⟩
  else
    .error s!"Uneven line length in `{lines}`"

def scoreAndRating (grid: Grid h w) (src: Coord h w): ℕ × ℕ :=
  let (allReachableTrailheads, rating) := go src
  (allReachableTrailheads.size, rating)
where
  go src: Std.HashSet (Coord h w) × ℕ :=
    let (y, x) := src
    let height := grid[y][x]
    match hyp: height.val with
    | 0 => ({ src }, 1)
    | k + 1 =>
      let nextHeight: Fin 10 := ⟨k,
        lt_trans (Nat.lt_succ_self k) (hyp ▸ height.isLt)⟩
      src.neighbors
        |>.filter (fun (y', x') => grid[y'][x'] = nextHeight)
        |>.attach
        |>.map (fun ⟨(y', x'), hc⟩ =>
          have: grid[y'][x'] < grid[y][x] := by
            simp at hc
            rw [Fin.lt_def, hyp]
            simp [hc.right]

          go (y', x'))
        |>.foldl (init := ({}, 0))
          fun (accSet, accRating) (set, rating) =>
            (accSet ∪ set, accRating + rating)
  termination_by grid[src.fst][src.snd]

def ans₁: IO ℕ := do
  let ⟨h, w, grid⟩ ← grid
  return Coord.all h w
    |>.filter (fun (y, x) => grid[y][x] = 9)
    |>.map (fun c => (scoreAndRating grid c).fst)
    |>.fold (· + ·) 0

#eval ans₁

def ans₂: IO ℕ := do
  let ⟨h, w, grid⟩ ← grid
  return Coord.all h w
    |>.filter (fun (y, x) => grid[y][x] = 9)
    |>.map (fun c => (scoreAndRating grid c).snd)
    |>.fold (· + ·) 0

#eval ans₂
