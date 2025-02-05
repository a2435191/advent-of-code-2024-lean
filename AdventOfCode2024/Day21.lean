import AdventOfCode2024.Basic
import Mathlib.Data.Nat.Digits

def data := load "AdventOfCode2024/Inputs/Day21.txt"

inductive NumericKeypad
| num: Fin 10 → NumericKeypad
| gap
| activate
deriving Repr, DecidableEq

namespace NumericKeypad

def toCoord: NumericKeypad → Coord 4 3
| .num 0 => (3, 1)
| .num n =>
  let y := 2 - (n.val - 1) / 3
  have hy := trans
    (Nat.sub_le 2 ((n.val - 1) / 3))
    (show 2 < 4 by decide)

  let x := (n - 1).modn 3
  have hx := Fin.modn_lt _ (show 0 < 3 by decide)

  (⟨y, hy⟩, ⟨x, hx⟩)
| .gap => (3, 0)
| .activate => (3, 2)

def ofChar: Char → Except String NumericKeypad
| '0' => .ok <| .num 0
| '1' => .ok <| .num 1
| '2' => .ok <| .num 2
| '3' => .ok <| .num 3
| '4' => .ok <| .num 4
| '5' => .ok <| .num 5
| '6' => .ok <| .num 6
| '7' => .ok <| .num 7
| '8' => .ok <| .num 8
| '9' => .ok <| .num 9
| 'A' => .ok .activate
| c => .error s!"`{c}` is not a valid character for a `NumericKeypad`"

end NumericKeypad

def nkTargets: IO (List (List NumericKeypad)) :=
  (data
  >>= List.mapM (fun s => do
    let target ← monadLift <| s.toList.mapM NumericKeypad.ofChar
    if target.getLast? = some .activate then
      return target
    throw <| .userError
      s!"assumption: the input targets all end
with `A` (got {target.getLast?.repr 0} instead)"))

def List.reversePairs (l: List α): List (α × α) :=
  go [] l
where
  go (acc: List (α × α)): List α → List (α × α)
  | [] => []
  | [_] => acc
  | x :: y :: rest => go ((x, y) :: acc) (y :: rest)

def List.pairs: List α → List (α × α) :=
  List.reverse ∘ List.reversePairs

inductive DirectionalKeypad
| up | dn | lf | rt
| gap
| activate
deriving DecidableEq, Hashable, Ord

namespace DirectionalKeypad
instance : ToString DirectionalKeypad where
  toString
  | .up => "^"
  | .dn => "v"
  | .lf => "<"
  | .rt => ">"
  | .gap => "X"
  | .activate => "A"

instance : Repr DirectionalKeypad where
  reprPrec x _ := toString x


instance : ToString (List DirectionalKeypad) where
  toString l :=
    if l.isEmpty then "∅"
    else String.join (List.map toString l)

def toCoord: DirectionalKeypad → Coord 2 3
| .gap      => (0, 0)
| .up       => (0, 1)
| .activate => (0, 2)
| .lf       => (1, 0)
| .dn       => (1, 1)
| .rt       => (1, 2)

def possibleNext (cur tgt: Coord h w): List (DirectionalKeypad × Coord h w) :=
  let (y₁, x₁) := cur
  let (y₂, x₂) := tgt
  let yMove: Option (DirectionalKeypad × Coord h w) :=
    match compare y₁ y₂ with
    | .lt => some ⟨.dn, y₁.addNat' 1, x₁⟩
    | .eq => none
    | .gt => some ⟨.up, y₁.pred', x₁⟩

  let xMove: Option (DirectionalKeypad × Coord h w) :=
    match compare x₁ x₂ with
    | .lt => some ⟨.rt, y₁, x₁.addNat' 1⟩
    | .eq => none
    | .gt => some ⟨.lf, y₁, x₁.pred'⟩

  yMove.toList ++ xMove.toList

/--Each inner list (move sequence) is in reverse order.-/
partial def moves (src dst avoid: Coord h w): List (List DirectionalKeypad) :=
  go src dst [[]]
where
  go (cur tgt: Coord h w) (soFar: List (List DirectionalKeypad)): List (List DirectionalKeypad) :=
    -- dbg_trace "{cur} {tgt} {soFar}"
    if cur = avoid then
      -- dbg_trace "avoid"
      []
    else if cur = tgt then
      -- dbg_trace "equal"
      soFar
    else
      -- dbg_trace "possibleNext = {possibleNext cur tgt}"
      possibleNext cur tgt
        |>.map (fun (move, next) => go next tgt (soFar.map (move :: ·)))
        |>.flatten

-- Brute force all paths that hit a sequence of points
def type (avoid: Coord h w): List (Coord h w) → List (List DirectionalKeypad)
| [] | [_] => [[]]
| src :: dst :: rest =>
  moves src dst avoid
    |>.map (List.reverse ∘ List.cons .activate)
    |>.product (type avoid (dst :: rest))
    |>.map (fun (new, old) => new ++ old)

structure Key where
  src: DirectionalKeypad
  dst: DirectionalKeypad
  index: ℕ -- decreasing index corresponds to higher `nMiddleRobots`
deriving BEq, Hashable, Repr

def all := [activate, up, dn, lf, rt]
def buildShortestSequenceLengths (nMiddleRobots: ℕ): Std.HashMap Key ℕ :=
  let initMap := Std.HashMap.ofList <|
      (all.product all|>.map (fun (x, y) => (⟨x, y, nMiddleRobots + 1⟩, 1)))
  go nMiddleRobots initMap
where
  go index soFar :=
    let new := (all.product all)
      |>.map (fun (src, dst) =>
        let pairs :=
          moves src.toCoord dst.toCoord gap.toCoord
          |>.map (fun seq => activate :: (activate :: seq).reverse)
          |>.map List.pairs
        let shortestLength := pairs
          |>.map (List.map fun (src', dst') => soFar.get! ⟨src', dst', index + 1⟩)
          |>.map List.sum
          |>.min?
          |>.get!
        ({ src, dst, index }, shortestLength))
      |> Std.HashMap.ofList
    match index with
    | 0 => soFar ∪ new
    | k + 1 => go k (soFar ∪ new)

end DirectionalKeypad

def calculateScore (targets: List (List NumericKeypad)) (nMiddleRobots: ℕ): ℕ :=
  let lengths := DirectionalKeypad.buildShortestSequenceLengths nMiddleRobots
  targets
    |>.map (fun l =>
      let numericPart := l
        |>.filterMap (fun
          | .num n => some n.val
          | _ => none)
        |>.reverse
        |> Nat.ofDigits 10

      let directionalTargets := DirectionalKeypad.type
        NumericKeypad.gap.toCoord
        ((.activate :: l).map NumericKeypad.toCoord)
      let shortestLength := directionalTargets
        |>.map (List.cons .activate)
        |>.map List.pairs
        |>.map (List.map (
          fun (cur, nxt) => lengths.get! ⟨cur, nxt, 1⟩))
        |>.map List.sum
        |>.min?
        |>.get!

      -- dbg_trace "{repr l} {shortestLength} * {numericPart}"
      shortestLength * numericPart)
    |>.sum

def ans₁: IO ℕ := do
  return calculateScore (←nkTargets) 2

def ans₂: IO ℕ := do
  return calculateScore (←nkTargets) 25

#eval ans₁
#eval ans₂
