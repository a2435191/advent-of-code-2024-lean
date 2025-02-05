import AdventOfCode2024.Basic

def input := load "AdventOfCode2024/Inputs/Day16.txt"

def grid: IO Maze :=
  input >>= (liftM ∘ Maze.parse)

structure Node (h w: ℕ) extends Coord h w where
  facing: Coord.Facing
deriving BEq, Repr, Hashable, DecidableEq

def Node.all (c: Coord h w): List (Node h w) :=
  Coord.Facing.all.map (Node.mk c)

def edgesForCoord (verts: Std.HashSet (Coord h w)) (v: Coord h w): List (Node h w × Array (Node h w × ℕ)) :=
  Coord.Facing.all
    |>.map fun f =>
      let (adj₁, adj₂) := match f with
        | .north | .south => (.east, .west)
        | .east  | .west  => (.north, .south)
      let selfEdges := #[(Node.mk v adj₁, 1000), (Node.mk v adj₂, 1000)]
      let edges :=
        match Coord.neighborFacing v f with
        | none => selfEdges
        | some u =>
          if u ∈ verts then selfEdges.push (Node.mk u f, 1)
          else selfEdges
      (Node.mk v f, edges)


def ans₁: IO ℕ := do
  let grid ← grid
  let edges := grid.track.toList
    |>.map (edgesForCoord grid.track)
    |>.flatten
    |> Std.HashMap.ofList
  let (dist, _) := dijkstra
    (edges.getD · #[])
    (Node.mk grid.start .east)
  let some shortestDist := grid.end
    |> Node.all
    |>.filterMap dist
    |>.min?
    | .error s!"No minimum-distance path found"
  return shortestDist

#eval ans₁

/-- Modification of `dijkstra` in `Basic.lean` to return all shortest paths,
    so that `prev[v]` holds all neighbors that lie on a shortest path through `v`.-/
def dijkstraAll [BEq α] [Hashable α] (edges: α → Array (α × Nat)) (src: α) := Id.run do
  let mut dist: Std.HashMap α Nat := { (src, 0) }
  let mut prev: Std.HashMap α (List α) := {  }
  let mut queue: Batteries.BinaryHeap (α × Nat) (·.2 > ·.2) := .insert ∅ (src, 0)

  while true do
    let max := queue.max
    queue := queue.popMax
    match max with
    | none => break
    | some (u, uDist) =>
      for (v, uvEdgeDist) in edges u do
        let distThrough_uv := uDist + uvEdgeDist
        if Option.all (distThrough_uv < ·) (dist.get? v) then
          dist := dist.insert v distThrough_uv;
          prev := prev.insert v [u];
          queue := queue.insert (v, distThrough_uv)
        else if dist.get? v = some distThrough_uv then
          prev := prev.modify v (List.cons u)

    ()

  (dist.get?, prev.get?)

partial def allPaths (prev: α → Option (List α)) (dst: α): List (List α) :=
  match prev dst with
  | none => [[dst]]
  | some neighbors =>
    neighbors
      |>.flatMap (allPaths prev)
      |>.map (List.cons dst)

def ans₂: IO ℕ := do
  let grid ← grid
  let edges := grid.track.toList
    |>.map (edgesForCoord grid.track)
    |>.flatten
    |> Std.HashMap.ofList
  let (dist, paths) := dijkstraAll
    (edges.getD · #[])
    (Node.mk grid.start .east)
  let some shortestDist := grid.end
    |> Node.all
    |>.filterMap dist
    |>.min?
    | .error s!"No minimum-distance path found"
  let endNodesWithMinDist := grid.end
    |> Node.all
    |>.filter (dist · = shortestDist)

  let shortestPaths := endNodesWithMinDist
    |>.flatMap (allPaths paths)

  let coordsOnAnyShortestPaths := shortestPaths
    |>.flatten
    |>.map (Node.toProd)
    |> Std.HashSet.ofList

  -- for hi: i in [0:grid.h] do
  --   let i' := Fin.mk i (Membership.get_elem_helper hi rfl)
  --   for hj: j in [0:grid.w] do
  --     let j' := Fin.mk j (Membership.get_elem_helper hj rfl)
  --     if (i', j') ∈ coordsOnAnyShortestPaths then
  --       IO.print "O"
  --     else if (i', j') ∈ grid.track then
  --       IO.print "."
  --     else
  --       IO.print "#"
  --   IO.print "\n"

  return coordsOnAnyShortestPaths.size

#eval ans₂
