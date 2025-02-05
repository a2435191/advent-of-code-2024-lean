import AdventOfCode2024.Basic
import Std.Data.HashSet.Basic

def data := load "AdventOfCode2024/Inputs/Day18.txt"

def pairsOfList (size: Nat): List Nat → IO (Coord size size)
| [x, y] =>
  if h: x < size ∧ y < size then
    pure (⟨x, h.left⟩, ⟨y, h.right⟩)
  else
    throw <| .userError s!"{[x, y]}"
| l => throw <| .userError s!"{l}"

def points (size: Nat): IO (List (Coord size size)) := do
  (←data).mapM (fun line => do
    let pairs ← (line.splitOn ",").mapM (monadLift ∘ String.toNat?')
    pairsOfList size pairs)

def shortestPath {size: Nat} (obstacles: Std.HashSet (Coord size size)) (src dst: Coord size size) :=
  let (_, prev) := dijkstra
    (fun coord =>
      (Coord.neighbors coord)
        |>.toArray
        |>.filter (· ∉ obstacles)
        |>.map ((·, 1)))
    src
  pathTo dst prev

def ans₁ := do
  let pts := (←points 71).take 1024
  let path := shortestPath
    (Std.HashSet.ofList pts)
    (Coord.upperLeft (by decide) (by decide))
    (Coord.lowerRight (by decide) (by decide))
  return path.length - 1

def ans₂ := do
  let pts := (←points 71)
  let mut obstacles := {  }
  let src := Coord.upperLeft (by decide) (by decide)
  let dst := Coord.lowerRight (by decide) (by decide)
  for pt in pts do
    obstacles := Std.HashSet.insert obstacles pt
    let path := shortestPath obstacles src dst
    if path.head? ≠ some src then
      return s!"{pt.1},{pt.2}"
  .error <| IO.userError "Couldn't find blocking point"
