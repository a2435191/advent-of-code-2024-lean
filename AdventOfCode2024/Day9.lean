import AdventOfCode2024.Basic

def input := loadAsString "AdventOfCode2024/Inputs/Day9.txt"

inductive Block
| file (id: ℕ)
| free
deriving Inhabited, BEq

instance : Repr (List (Block × ℕ)) where
  reprPrec lst _ :=
    if lst.isEmpty then "∅"
    else String.intercalate "" <| lst.map fun
      | (.free, len) => String.replicate len '.'
      | (.file id, len) => String.intercalate "" <| List.replicate len (toString id)

/-- Returns the run-length encoding in reverse order -/
def blocksRLE: IO (List (Block × ℕ)) := do
  let chars ← input
  let digits ← chars.toList.mapM (liftM ∘ Char.toNat?)
  return go [] true 0 digits
where
  go acc indicatesFile id: List (Fin 10) → List (Block × ℕ)
  | [] => acc
  | x :: xs =>
    if indicatesFile then
      go ((.file id, x) :: acc) false id xs
    else
      go ((.free, x) :: acc) true (id + 1) xs

/-- Returns in forward order -/
partial def rearrange (reversed: List (Block × ℕ)): List (Block × ℕ) :=
  go reversed.reverse reversed 0 (reversed.map (·.2)|>.sum) [] []
where
  go front back i j frontAcc backAcc :=
    -- dbg_trace "go front = {repr front} back = {repr back} i = {i} j = {j} frontAcc = {repr frontAcc} backAcc = {repr backAcc}"
    if i < j then
      match front, back with
      | [], _ | _, [] => panic s!"{repr front} {repr back}"
      | (.file id, n) :: front', _ =>
        -- dbg_trace "here 1"
        let Δ := min n (j - i)
        go
          front' back
          (i + Δ) j
          ((.file id, Δ) :: frontAcc) backAcc
      | _, (.free, m) :: back' =>
        -- dbg_trace "here 2"
        let Δ := min m (j - i)
        go
          front back'
          i (j - Δ)
          frontAcc ((.free, Δ) :: backAcc)
      | (.free, n) :: front', (.file id, m) :: back' =>
        if n < m then
          -- dbg_trace "{n} < {m}"
          let Δ := min n (j - i)
          go
            front' ((.file id, m - Δ) :: back')
            (i + Δ) (j - Δ)
            ((.file id, Δ) :: frontAcc) ((.free, Δ) :: backAcc)
        else if n = m then
          -- dbg_trace "{n} = {m}"
          let Δ := min n (j - i)
          go
            front' back'
            (i + Δ) (j - Δ)
            ((.file id, Δ) :: frontAcc) ((.free, Δ) :: backAcc)
        else -- n > m
          -- dbg_trace "{n} > {m}"
          let Δ := min m (j - i)
          go
            ((.free, n - Δ) :: front') back'
            (i + Δ) (j - Δ)
            ((.file id, Δ) :: frontAcc) ((.free, Δ) :: backAcc)
    else
      frontAcc.reverse ++ backAcc.reverse

class Foldl (F: Type u → Type v) where
  foldl (f: α → β → α) (init: α) (seq: F β): α

instance : Foldl List := ⟨List.foldl⟩
instance : Foldl Array := ⟨Array.foldl⟩

def checkSum [inst: Foldl F] (seq: F (Block × ℕ)): ℕ :=
  Prod.snd <| inst.foldl (init := (0, 0)) (seq := seq) fun
    | (idx, acc), (.free, n) => (idx + n, acc)
    | (idx, acc), (.file id, n) => (idx + n, acc + (List.range' idx n).sum * id)

def ans₁ := do
  let rearranged := rearrange (←blocksRLE)
  return checkSum rearranged

-- #eval ans₁

def rearrange' (reversed: List (Block × ℕ)): Array (Block × ℕ) :=
  let FoldT (arr: Array (Block × ℕ)) :=
    (id: ℕ)
    × (fileWidth: ℕ)
    × (i: Fin arr.size)
    ×' (arr[i] = (.file id, fileWidth))
  reversed
    |>.filterMap (fun
      | (.free, _) => none
      | (.file id, n) => some (id, n))
    |>.foldl (init := reversed.toArray) fun arr (id, fileWidth) => Id.run do
      let some i := arr.indexOf? (.file id, fileWidth) | panic "rearrange'"
      let mut jAndFreeWidth?: Option (Fin arr.size × ℕ) := none
      for hk: k in [i + 1 : arr.size] do
        match arr[k] with
        | (.file _, _) => ()
        | (.free, freeWidth) =>
          if freeWidth ≥ fileWidth then
            jAndFreeWidth? := some (⟨k, Membership.get_elem_helper hk rfl⟩, freeWidth)
      if let some (j, freeWidth) := jAndFreeWidth? then
        if freeWidth = fileWidth then
          arr.swap i j
        else -- freeWidth > fileWidth
          arr
            |>.set i (.free, fileWidth)
            |>.set j (.file id, fileWidth)
            |>.insertIdx j (.free, freeWidth - fileWidth)
            -- |> compactFrees
      else
        arr
where
  compactFrees (arr: Array (Block × ℕ)) :=
    List.toArray <| List.reverse <| Prod.fst <|
      arr.foldl (init := ([], none)) fun
        | (acc, none), (.free, n) => (acc, some n)
        | (acc, some freeLength), (.free, n) => (acc, some (freeLength + n))
        | (acc, none), x@(.file _, _) => (x :: acc, none)
        | (acc, some freeLength), x@(.file _, _) => (x :: (.free, freeLength) :: acc, none)

def ans₂ := do
  let rearranged := rearrange' (←blocksRLE)
  return checkSum rearranged.reverse.toList

-- #eval ans₂
