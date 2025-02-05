import AdventOfCode2024.Basic

def input := loadAsString "AdventOfCode2024/Inputs/Day15.txt"

inductive Warehouse.FloorType | empty | solid
deriving DecidableEq, Repr, BEq

inductive Warehouse.ParseType | tile | box | wall | robot
deriving DecidableEq

structure Warehouse (h w: ℕ) where
  track: Std.HashMap (Coord h w) Warehouse.FloorType
  robotPosition: Coord h w

instance : Repr (Warehouse h w) where
  reprPrec wh _ :=
    let getChar c :=
      if c = wh.robotPosition then '@'
      else
        match wh.track[c]? with
        | none => '#'
        | some .solid => 'O'
        | some .empty => '.'

    let is := List.range h
      |>.attach
      |>.map (fun ⟨i, hi⟩ => Fin.mk i (List.mem_range.mp hi))
    let js := List.range w
      |>.attach
      |>.map (fun ⟨j, hj⟩ => Fin.mk j (List.mem_range.mp hj))

    is
      |>.map (fun i =>
        String.mk <| js.map (fun j => getChar (i, j)))
      |> String.intercalate "\n"


namespace Warehouse

def parse (lines: List String): Except String ((h: ℕ) × (w: ℕ) × Warehouse h w) := do
  let w := (String.length <$> lines.head?).getD 0
  if hw: ∀ line ∈ lines, line.length = w then
    let grid ← Except.mapError reprStr <|
      Grid.parse lines rfl hw fun c => fun
        | '#' => some (c, ParseType.wall)
        | '.' => some (c, .tile)
        | 'O' => some (c, .box)
        | '@' => some (c, .robot)
        | _   => none

    let [(robotPosition, _)] := grid.filter fun (_, tt) => tt = .robot
      | .error "Not exactly one robot position found"

    let track := .ofList <| grid.filterMap fun
        | (c, .tile) => some (c, .empty)
        | (c, .box) | (c, .robot) => some (c, .solid)
        | (_, .wall) => none

    return ⟨lines.length, w, { track, robotPosition }⟩
  else
    .error "Uneven line length"

partial def tryMove {h w} (wh: Warehouse h w) (move: Coord.Facing): Option (Warehouse h w) :=
  match Coord.neighborFacing wh.robotPosition move with
  | none => none -- out of bounds
  | some targetPos =>
    match wh.track[targetPos]? with
    | none => none -- wall
    | some .empty => some { robotPosition := targetPos,
                            track := wh.track
                                  |>.insert wh.robotPosition .empty
                                  |>.insert targetPos .solid }
    | some .solid =>
      match tryMove { wh with robotPosition := targetPos} move with
      | none => none
      | some wh' =>
        some { robotPosition := targetPos,
               track := wh'.track
                        |>.insert wh.robotPosition .empty
                        |>.insert targetPos .solid }

end Warehouse

def movesAndWarehouse: IO (List Coord.Facing × (h: ℕ) × (w: ℕ) × Warehouse h w) := do
  let inputStr ← input
  let [gridStr, movesStr] := inputStr.splitOn "\n\n"
    | .error s!"Could not split `{inputStr}` into two"
  let wh ← Warehouse.parse (gridStr.splitOn "\n")
  let moves ← movesStr.toList.filterMapM fun
    | '^' => return some .north
    | 'v' => return some .south
    | '<' => return some .west
    | '>' => return some .east
    | '\n' => return none
    | c   => .error s!"Unknown character `{c}` for direction"

  return (moves, wh)

def ans₁: IO ℕ := do
  let ⟨moves, _, _, initWarehouse⟩ ← movesAndWarehouse
  let result := moves.foldl
    (fun wh move => (Warehouse.tryMove wh move).getD wh)
    initWarehouse

  return result.track
    |>.filter (fun c v => v = .solid ∧ c ≠ result.robotPosition)
    |>.keys
    |>.map (fun (y, x) => 100 * y + x)
    |>.sum

#eval ans₁
namespace Warehouse

structure Wide (h w: ℕ) extends Warehouse h w where
  links: Std.HashMap (Coord h w) (Coord h w)

instance : Repr (Wide h w) where
  reprPrec wide _ :=
    let getChar c :=
      if c = wide.robotPosition then '@'
      else
        match wide.track[c]? with
        | none => '#'
        | some .solid =>
          if let some (_, x') := wide.links[c]? then
            if c.2 < x' then '[' else ']'
          else '?'
        | some .empty => '.'

    let is := List.range h
      |>.attach
      |>.map (fun ⟨i, hi⟩ => Fin.mk i (List.mem_range.mp hi))
    let js := List.range w
      |>.attach
      |>.map (fun ⟨j, hj⟩ => Fin.mk j (List.mem_range.mp hj))

    is
      |>.map (fun i =>
        String.mk <| js.map (fun j => getChar (i, j)))
      |> String.intercalate "\n"

def widen (wh: Warehouse h w): Wide h (2 * w) :=
  let mul2 {a} (x: Fin a): Fin (2 * a) :=
    ⟨x + x, by simp [Nat.two_mul, Nat.add_lt_add]⟩
  let mul2PlusOne {a} (x: Fin a): Fin (2 * a) :=
    ⟨x + x + 1, by simp [Nat.two_mul, Nat.add_assoc,
                         Nat.add_lt_add_of_lt_of_le,
                         Nat.add_one_le_of_lt]⟩
  let (robotY, robotX) := wh.robotPosition
  let robotPosition := (robotY, mul2 robotX)

  let lst := wh.track
    |>.toList
    |>.map (fun (c@(y, x), ft) =>
      let (ft'₁, ft'₂) := match ft with
        | .empty => (FloorType.empty, FloorType.empty)
        | .solid =>
          if c = wh.robotPosition then (.solid, .empty)
          else (.solid, .solid)
      (((y, mul2 x), ft'₁), ((y, mul2PlusOne x), ft'₂)))

  let links := lst
    |>.filter (fun ((_, ft₁), (_, ft₂)) => ft₁ = .solid && ft₂ = .solid)
    |>.map (fun ((c₁, _), (c₂, _)) => (c₁, c₂))
    |>.foldr (fun (c₁, c₂) acc => (c₁, c₂) :: (c₂, c₁) :: acc) []
    |> Std.HashMap.ofList
  let track := lst
    |>.foldr (fun (z₁, z₂) acc => z₁ :: z₂ :: acc) []
    |> Std.HashMap.ofList
    |>.insert robotPosition .solid

  { toWarehouse := { track, robotPosition } , links }

private def updateTrack (track: Std.HashMap (Coord h w) FloorType) (old new: Coord h w) :=
  track
    |>.insert new .solid
    |>.insert old .empty

private def replaceLinks (links:  Std.HashMap (Coord h w) (Coord h w)) (k₁ k₂ k₁' k₂': Coord h w) :=
  links
    |>.erase k₁
    |>.erase k₂
    |>.insert k₁' k₂'
    |>.insert k₂' k₁'

partial def tryMoveWithLinks {h w} (wide: Wide h w) (move: Coord.Facing): Option (Wide h w) :=
  go wide.robotPosition wide.track wide.links true <&>
    fun (robotPosition, track, links) =>
      Wide.mk { robotPosition, track } links
where
  go pos track links calcLinked := do
    --dbg_trace "here {pos} {calcLinked} {repr links}:"

    let print
    | (pos, trk, lks) =>
      --dbg_trace "{repr <| Wide.mk { robotPosition := wide.robotPosition, track := trk } lks}"
      (pos, trk, lks)
    let target ← pos.neighborFacing move
    match links[pos]? with
    | none =>
      match ←track[target]? with
      | .empty =>
        --dbg_trace "returning from none -> empty"
        return print (target, updateTrack track pos target, links)
      | .solid =>
        let (_, track', links') ← go target track links true
        --dbg_trace "returning from none -> solid"
        return print (target, updateTrack track' pos target, links')
    | some linked =>
      match ←track[target]? with
      | .empty =>
        if calcLinked then
          let (linkedPos, track', links') ← go linked track links false
          --dbg_trace "returning from some -> empty -> true"
          return print (target,
            updateTrack track' pos target,
            replaceLinks links' pos linked linkedPos target)
        else
          --dbg_trace "returning from some -> empty -> false"
          return print (target,
            updateTrack track pos target,
            links)
      | .solid =>
        if target = linked then
          let (newLinkedPos, track', links') ← go linked track links false
          --dbg_trace "returning from some -> solid -> true"
          return print (target,
            updateTrack track' pos target,
            replaceLinks links' pos linked newLinkedPos target)
        else
          let (_, track', links') ← go target track links true
          if calcLinked then
            let (linkedPos, track'', links'') ← go linked track' links' false
            --dbg_trace "returning from some -> solid -> false -> true"
            return print (target,
              updateTrack track'' pos target,
              replaceLinks links'' pos linked linkedPos target)
          else
            --dbg_trace "returning from some -> solid -> false -> false"
            return print (target,
              updateTrack track' pos target,
              links')
end Warehouse

def ans₂: IO ℕ := do
  let ⟨moves, _, _, initWarehouse⟩ ← movesAndWarehouse
  let initWide := Warehouse.widen initWarehouse
  -- println! s!"{repr initWide}\n{repr initWide.links}\n"
  let wide' := moves.foldl (init := initWide) fun wide move =>
    (Warehouse.tryMoveWithLinks wide move).getD wide
  -- IO.println s!"{repr wide'}\n{repr wide'.links}\n"
  let boxLeftEdges ← wide'.track
    |>.toList
    |>.filterM (fun (c@(_, x), ft) =>
      if !(ft = Warehouse.FloorType.solid && c ≠ wide'.robotPosition) then
        return false
      else match wide'.links[c]? with
        | some (_, ⟨x', _⟩) => return x.val + 1 == x'
        | none => .error s!"`c` = `{c}` is not `robotPosition` \
                           but is not present in `wide.links` either")

  return boxLeftEdges
    |>.map (fun ((y, x), _) => 100 * y + x)
    |>.sum

#eval ans₂


#eval (2: Fin 5) + (4: Fin 5)
