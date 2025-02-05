import AdventOfCode2024.Basic

def data := load "AdventOfCode2024/Inputs/Day23.txt"

def connections := data >>= List.mapM fun line =>
  match line.splitOn "-" with
  | [c₁, c₂] => pure (c₁, c₂)
  | _ => throw <| IO.userError s!"line `{line}` could not be split into two parts"

abbrev Edges := Std.HashMap String (Std.HashSet String)

def Edges.ofPairs (pairs: List (String × String)): Edges :=
  pairs.foldr (fun (c₁, c₂) acc =>
    acc
      |>.alter c₁ (fun
        | none => some { c₂ }
        | some s => s.insert c₂)
      |>.alter c₂ (fun
        | none => some { c₁ }
        | some s => s.insert c₁)
  ) {}

def ans₁ := do
  let edges := Edges.ofPairs (←connections)
  return edges
    |>.map (fun k₁ v =>
      let neighbors := Std.HashSet.toList v
      let pairs: List (String × String) := List.product neighbors neighbors
      pairs
        |>.filterMap (α := String × String) (fun (k₂, k₃) =>
          if k₁ < k₂ ∧ k₂ < k₃ ∧ k₂ ∈ edges[k₃]! then
            some (k₁, k₂, k₃)
          else
            none))
    |>.values
    |>.flatten
    |>.filter (α := (String × String × String)) (fun (k₁, k₂, k₃) => k₁.head = 't' ∨ k₂.head = 't' ∨ k₃.head = 't')
    |>.length

#eval ans₁

-- Bron-Kerbosch algorithm
partial def biggestClique (edges: Edges): Option (Std.HashSet String) :=
  go {} (.ofList edges.keys) {}
where
  go (r p x: Std.HashSet String) :=
    if p.isEmpty ∧ x.isEmpty then some r
    else
      let (biggest, _, _) := p.fold (init := (none, p, x))
        fun (biggestSoFar, p, x) v =>
          let vNeighbors := edges[v]!
          let next := go (r.insert v) (p ∩ vNeighbors) (x ∩ vNeighbors)
          let nextBiggest :=
            match next, biggestSoFar with
            | none, none => none
            | none, some s => s
            | some s, none => s
            | some s₁, some s₂ => if s₁.size > s₂.size then s₁ else s₂
          (nextBiggest, p.erase v, x.insert v)
      biggest

def ans₂ := do
  let edges := Edges.ofPairs (←connections)
  return biggestClique edges
    |>.get!
    |>.toList
    |>.mergeSort
    |> String.intercalate ","
