import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Batteries.Data.BinaryHeap
import Batteries.Data.String.Lemmas
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Fold

@[inline]
def Function.repeat (f: α → α) (init: α) (n: ℕ) :=
  match n with
  | 0 => init
  | k + 1 => Function.repeat f (f init) k

lemma Option.length_toList: (Option.toList o).length ≤ 1 := by
  unfold toList
  split
  · simp only [List.length_nil, Nat.zero_le]
  · simp only [List.length_singleton, Nat.le_refl]

instance : DecidableRel Int.lt :=
  fun x y => by unfold Int.lt; infer_instance

@[inline]
def Fin.pred' (a: Fin n) :=
  Fin.mk (↑a - 1) (trans (Nat.pred_le _) a.isLt)

@[inline]
def Fin.succ' (a: Fin n) (h: a.succ ≠ last n): Fin n :=
  Fin.castLT (Fin.succ a) (val_lt_last h)

@[inline]
def Fin.subNat' (a: Fin n) (b: Nat): Fin n :=
  if h: b ≤ a then a - ⟨b, trans h a.2⟩
  else ⟨0, Fin.pos a⟩

@[inline]
def Fin.addNat' (a: Fin n) (b: Nat): Fin n :=
  if h: a + b < n then ⟨a + b, h⟩
  else ⟨n - 1, Nat.sub_one_lt_of_lt (Fin.pos a)⟩

/-- Inclusive -/
@[inline]
def MLList.finRange [Monad m] (start stop: Fin n): MLList m (Fin n) :=
  MLList.fix? (fun k => pure (
    let k' := k.val.succ
    if h: k' ≤ stop then
      some ⟨k', trans h stop.isLt⟩
    else none
  )) start

@[inline]
def MLList.length [Monad m] (l: MLList m α) :=
  MLList.fold (fun n _ => n + 1) 0 l

abbrev Coord (h w: Nat) := Fin h × Fin w
namespace Coord
def upperLeft (hpos: 0 < h) (wpos: 0 < w): Coord h w := (⟨0, hpos⟩, ⟨0, wpos⟩)
def lowerRight (hpos: 0 < h) (wpos: 0 < w): Coord h w :=
  (⟨h - 1, Nat.sub_one_lt_of_lt hpos⟩, ⟨w - 1, Nat.sub_one_lt_of_lt wpos⟩)

def mk (x y: ℕ) (hx: x < h := by decide) (hy: y < w := by decide): Coord h w :=
  (⟨x, hx⟩, ⟨y, hy⟩)

def all (h w: Nat): MLList Id (Coord h w) :=
  (MLList.fin h).bind (fun a =>
    (MLList.fin w).map (Prod.mk a))

@[inline]
def neighbors: Coord h w → List (Coord h w)
| (a, b) =>
  let l1 := if ↑a = 0 then [] else (a.pred', b) :: []
  let l2 := if ↑b = 0 then l1 else (a, b.pred') :: l1
  let l3 := if ha: a.succ = Fin.last h then l2 else (a.succ' ha, b) :: l2
  let l4 := if hb: b.succ = Fin.last w then l3 else (a, b.succ' hb) :: l3
  l4

theorem length_neighbors {c: Coord h w}: (neighbors c).length ≤ 4 := by
  dsimp only [neighbors]
  split_ifs <;> simp

inductive Facing | north | south | east | west
deriving BEq, Repr, Hashable, DecidableEq

@[inline]
def Facing.all :=
  [north, south, east, west]

def neighborFacing: Coord h w → Facing → Option (Coord h w)
| (y, x) => fun
  | .north => if ↑y = 0 then none else some (y.pred', x)
  | .west  => if ↑x = 0 then none else some (y, x.pred')
  | .south => if hy: y.succ = Fin.last h then none else (y.succ' hy, x)
  | .east  => if hx: x.succ = Fin.last w then none else (y, x.succ' hx)

@[inline]
def taxicabDist: Coord h w → Coord h w → Nat
| (x₁, y₁), (x₂, y₂) =>
  (Int.sub x₁ x₂).natAbs + (Int.sub y₁ y₂).natAbs

@[inline]
def withinTaxicabDist (maxDist: Nat) (c: Coord h w): MLList Id (Coord h w) :=
  let (cx, cy) := c
  .finRange
    (cx.subNat' maxDist)
    (cx.addNat' maxDist) >>= fun x =>
    let xDist := (Int.sub cx x).natAbs
    let maxYDist := maxDist - xDist
    MLList.finRange
      (cy.subNat' maxYDist)
      (cy.addNat' maxYDist)
    |>.map (x, ·)

end Coord

def Char.toNat?: Char → Option (Fin 10)
| '0' => some 0 | '1' => some 1 | '2' => some 2
| '3' => some 3 | '4' => some 4 | '5' => some 5
| '6' => some 6 | '7' => some 7 | '8' => some 8
| '9' => some 9 | _ => none

def String.toNat?' (s: String): Except String Nat :=
  match s.toNat? with
  | .some n => .ok n
  | .none => .error s!"could not parse `{s}` to `Nat`"

def String.toInt?' (s: String): Except String ℤ :=
  match s.toInt? with
  | some n => .ok n
  | none => .error s!"Could not parse `{s}` as `Int`"

set_option synthInstance.checkSynthOrder false in
instance [Repr ε]: MonadLiftT (Except ε) IO where
  monadLift
  | .ok x => pure x
  | .error e => .error (.userError (reprStr e))

instance : MonadLiftT Option IO where
  monadLift
  | some x => pure x
  | none => .error (.userError "Failed to get value in `Option` computation")

def Option.toExcept (msg: String): Option α → Except String α
| some a => .ok a
| none => .error msg

def loadAsString (path: System.FilePath) :=
  IO.FS.withFile path .read
  (fun handle => do return ← handle.readToEnd)

/-- Split by single newlines.-/
def load (path: System.FilePath) := do
  let str ← loadAsString path
  return str.crlfToLf.splitOn "\n"

/-- Split by double newlines.-/
def load' (path: System.FilePath) := do
  let str ← loadAsString path
  return str.crlfToLf.splitOn "\n\n"

instance [Inhabited α]: Inhabited (Thunk α) :=
  ⟨.mk (fun () => default)⟩

instance : Monad Thunk where
  pure := Thunk.pure
  bind := Thunk.bind

instance : LawfulMonad Thunk := by
  apply LawfulMonad.mk'
  all_goals
    repeat intro
    rfl

def List.enumFin (l: List α): List (Fin l.length × α) :=
  l.enum.attach.map (fun ⟨(i, x), h⟩ =>
    have ⟨hi, _⟩ := List.mem_enum h
    (⟨i, hi⟩, x))

def Traversable.minBy [Traversable t] (f: α → Option Nat) (l: t α): Option (α × Nat) :=
  Traversable.foldl
    (fun acc a =>
      match (acc, f a) with
      | (_, .none) => acc
      | (.none, .some n) => .some (a, n)
      | (.some (_, m), .some n) =>
        if m ≤ n then acc else .some (a, n))
    .none
    l

def dijkstra [BEq α] [Hashable α] (edges: α → Array (α × Nat)) (src: α) := Id.run do
  let mut dist: Std.HashMap α Nat := { (src, 0) }
  let mut prev: Std.HashMap α α := {  }
  let mut queue: Batteries.BinaryHeap (α × Nat) (·.2 > ·.2) := .insert ∅ (src, 0)

  while true do
    let max := queue.max
    queue := queue.popMax
    match max with
    | none => break
    | some (u, uDist) =>
      for (v, uvEdgeDist) in edges u do
        let distThrough_uv := uDist + uvEdgeDist
        let replace := Option.all (distThrough_uv < ·) (dist.get? v)
        if replace then
          dist := dist.insert v distThrough_uv;
          prev := prev.insert v u;
          queue := queue.insert (v, distThrough_uv)
    ()

  (dist.get?, prev.get?)

partial def pathTo (dst: α) (prev: α → Option α) :=
  go dst prev [dst]
where go dst prev acc :=
  match prev dst with
  | none => acc
  | some next => go next prev (next :: acc)

def Substring.Valid.bsize_drop_one {s: Substring} (h₁: s.Valid) (h₂: ¬s.isEmpty): (s.drop 1).bsize < s.bsize := by
  rw [Valid.bsize h₁, Valid.bsize (Valid.drop h₁ 1), Valid.data_drop h₁ 1]
  rw [Valid.isEmpty h₁] at h₂
  match h: s.toString.data with
  | [] =>
    apply False.elim ∘ h₂
    rw [show s.toString = .mk s.toString.data from rfl, h]
  | x :: xs =>
    rw [List.drop_one, List.tail_cons, String.utf8Len_cons, Nat.lt_add_right_iff_pos]
    exact Char.utf8Size_pos x

def Substring.mapM [Monad m] (f: Char → m α) (s: Substring) (h: s.Valid): m (List α) :=
  loop s [] h
where
  loop s acc (h: s.Valid) :=
    if s.isEmpty then pure acc.reverse
    else do
      loop (s.drop 1) ((←f s.front) :: acc) (Valid.drop h 1)
  termination_by s.bsize
  decreasing_by exact Valid.bsize_drop_one h ‹¬s.isEmpty›

def Std.HashSet.inter [BEq α] [Hashable α] (s₁ s₂: Std.HashSet α) :=
  s₂.filter (· ∈ s₁)

instance [BEq α] [Hashable α]: Inter (Std.HashSet α) where
  inter := Std.HashSet.inter

inductive Validate (ε: Type u) (α: Type v)
| ok: α → Validate ε α
| errors: List ε → Validate ε α

namespace Validate
instance : Applicative (Validate ε) where
  pure := .ok
  seq vf vx :=
    match vf, vx () with
    | .ok f, .ok x => .ok (f x)
    | .ok _, .errors errs => .errors errs
    | .errors errs, .ok _ => .errors errs
    | .errors errs₁, .errors errs₂ => .errors (errs₁ ++ errs₂)
end Validate

namespace Grid

inductive ParseError
| unknownChar (location: Coord h w) (c: Char)
deriving Repr

def parse (lines: List String)
  (hh: lines.length = h) (hw: ∀ line ∈ lines, line.length = w)
  (f: Coord h w → Char → Option α): Except ParseError (List α) :=

  List.flatten <$>
  lines.enum.attach.mapM fun ⟨(i, line), hi⟩ =>
    have ⟨hi, hline⟩ := hh ▸ List.mem_enum hi
    line.toList.enum.attach.mapM fun ⟨(j, c), hj⟩ =>

      have ⟨hj, _⟩: j < w ∧ _ :=
        hw line (List.mem_iff_getElem.mpr ⟨i, hh ▸ hi, hline.symm⟩)
        ▸ (show line.toList.length = line.length from rfl)
        ▸ List.mem_enum hj

      let coord := (⟨i, hi⟩, ⟨j, hj⟩)
      match f coord c with
      | none => .error (.unknownChar coord c)
      | some a => .ok a

end Grid

structure Maze where
  h: Nat
  w: Nat
  start: Coord h w
  «end»: Coord h w
  track: Std.HashSet (Coord h w)

namespace Maze

inductive ParseError
| base (err: Grid.ParseError)
| differentLengthRows
| notOneStart
| notOneEnd
deriving Repr

private inductive TileType | start | «end» | track | wall
deriving DecidableEq

def parse (lines: List String): Except ParseError Maze := do
  let w := (String.length <$> lines.head?).getD 0
  if hw: ∀ line ∈ lines, line.length = w then
    let grid ← Except.mapError .base <|
      Grid.parse lines rfl hw fun c => fun
        | 'S' => some (c, TileType.start)
        | 'E' => some (c, .end)
        | '.' => some (c, .track)
        | '#' => some (c, .wall)
        | _ => none
    let [(start, _)] := grid.filter fun (_, tt) => tt = .start
      | .error .notOneStart
    let [(«end», _)] := grid.filter fun (_, tt) => tt = .end
      | .error .notOneEnd
    let track := grid
      |>.filter (fun (_, tt) =>
        tt = .start || tt = .end || tt = .track)
      |>.map Prod.fst
      |> Std.HashSet.ofList

    return { h := lines.length, w, start, «end», track }
  else
    .error .differentLengthRows
end Maze
