import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day8.txt"

def antennas: IO ((h: ℕ) × (w: ℕ) × Std.HashMap Char (List (Coord h w))) := do
  let lines ← input
  let h := lines.length
  let w := (String.length <$> lines.head?).getD 0
  if hyp: ∀ line ∈ lines, line.length = w then
    let grid ← Grid.parse (w := w) lines rfl hyp
      fun coord ch => some (coord, ch)
    let map := grid
      |>.filter (Char.isAlphanum ∘ Prod.snd)
      |>.foldl (init := {}) fun acc (coord, ch) =>
        acc.alter ch fun
          | none => [coord]
          | some lst => coord :: lst
    return ⟨h, w, map⟩
  else
    .error "Uneven length"

/-- Returns next coordinate in the direction of `Δ` within the `h-w` box-/
@[inline] def nextCoord (coord: Coord h w) (Δ: ℤ × ℤ): Option (Coord h w) :=
  let (y, x) := coord
  let (Δy, Δx) := Δ
  match y + Δy, x + Δx with
  | .ofNat y', .ofNat x' =>
    if hyp: y' < h ∧ x' < w then
      some (⟨y', hyp.left⟩, ⟨x', hyp.right⟩)
    else none
  | _, _ => none

def antinodes
  (antennas: Std.HashMap Char (List (Coord h w)))
  (antinodesFromCoordPairs: Coord h w → Coord h w → List (Coord h w))
: List (Char × Coord h w) :=
  List.flatten <| Std.HashMap.values <| antennas.map fun ch coords =>
    let antinodeCoords := List.product coords coords
      |>.map fun (c₁, c₂) => antinodesFromCoordPairs c₁ c₂
    antinodeCoords.flatten.map (ch, ·)

def ans₁ := do
  let ⟨_, _, antennas⟩ ← antennas
  let antinodes := antinodes antennas fun (y₁, x₁) (y₂, x₂) =>
    if (y₁, x₁) = (y₂, x₂) then []
    else
      let Δy := Int.sub y₂ y₁
      let Δx := Int.sub x₂ x₁
      (nextCoord (y₂, x₂) (Δy, Δx)).toList

  return (antinodes.map Prod.snd).dedup.length

#eval ans₁

/-- In order from farthest to closest (including `coord` itself)
    in the direction of `Δ`, in `Δ`-sized steps -/
def nextCoords (coord: Coord h w) (Δ: ℤ × ℤ): List (Coord h w) :=
  if hΔ: Δ = (0, 0) then
    []
  else
    go coord [coord] hΔ
where
  go cur acc hΔ :=
    match _hnext: nextCoord cur Δ with
    | none => acc
    | some next => go next (next :: acc) hΔ

  termination_by show ℕ from match Δ with
    | (.negSucc _, _) => cur.1
    | (.ofNat (_ + 1), _) => h - cur.1
    | (0, .negSucc _) => cur.2.val
    | (0, .ofNat (_ + 1)) => w - cur.2
    | (0, 0) => 0 -- unreachable
  decreasing_by
    simp [nextCoord] at _hnext
    split at _hnext
    · rename_i y' x' hy'₁ hx'₁
      simp at _hnext
      obtain ⟨_, hnext⟩ := _hnext
      simp [←hnext]
      split
      case' h_1.intro.h_1 => rename_i a _ -- used for * below
      case' h_1.intro.h_3 => rename_i a
      all_goals
        apply Int.ofNat_lt.mp
        dsimp only [Int.ofNat_eq_coe] at hy'₁
        dsimp only [Int.ofNat_eq_coe] at hx'₁
        try have := Int.negSucc_lt_zero a -- * needed for omega in some cases
        first | contradiction | omega
    · contradiction

def ans₂ := do
  let ⟨_, _, antennas⟩ ← antennas
  let antinodes := antinodes antennas fun (y₁, x₁) (y₂, x₂) =>
    if (y₁, x₁) = (y₂, x₂) then []
    else
      let Δy := Int.sub y₂ y₁
      let Δx := Int.sub x₂ x₁
      let gcd := Int.gcd Δy Δx

      nextCoords (y₂, x₂) (Δy / gcd, Δx / gcd)

  return (antinodes.map Prod.snd).dedup.length

#eval ans₂
