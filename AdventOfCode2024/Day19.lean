import AdventOfCode2024.Basic
import Batteries.Data.String.Lemmas

inductive Color | w | u | b | r | g
deriving BEq, Hashable

instance : ToString Color where
  toString := fun
  | .w => "w"
  | .u => "u"
  | .b => "b"
  | .r => "r"
  | .g => "g"

def Color.ofChar: Char → IO Color
| 'w' => pure w
| 'u' => pure u
| 'b' => pure b
| 'r' => pure r
| 'g' => pure g
| c => throw <| .userError s!"Could not parse `{c}` to a `Color`"


def Color.listFromString (s: String): IO (List Color) :=
  Substring.mapM Color.ofChar s (String.valid_toSubstring _)

def data := load "AdventOfCode2024/Inputs/Day19.txt"

def towelInfos := do match ←data with
| hd :: "" :: rest =>
  let patterns := hd.splitOn ", "|>.mapM Color.listFromString
  let designs := rest.mapM Color.listFromString
  return (←patterns, ←designs)
| s => throw <| IO.Error.userError s!"{s}"

partial def countTowelDesigns (patterns: List (List Color)) (design: List Color): EStateM Empty (Std.HashMap (List Color) Nat) Nat := do
  match (←get).get? design with
  | some res => return res
  | none =>
    match design with
    | [] => modifyGet (1, ·.insert design 1)
    | _ =>
      let bestSplit := patterns
        |>.mapM (fun pre =>
          match design.dropPrefix? pre with
          | none => return 0
          | some suf => countTowelDesigns patterns suf)
      let result ← bestSplit
      let count := result.sum
      modifyGet (count, ·.insert design count)

def countTowelsDesigns (patterns: List (List Color)) (designs: List (List Color)): List Nat :=
  let (res, _) := designs.foldl (init := ([], .empty))
    fun (acc, cache) design =>
      match (countTowelDesigns patterns design).run cache with
      | .error .. => by contradiction -- error type is Empty
      | .ok res cache' => (res :: acc, cache')

  res.reverse

def answer := do
  let (patterns, designs) := ←towelInfos
  let counts := countTowelsDesigns patterns designs
  return (counts.filter (· ≠ 0)|>.length, counts.sum)

def ans₁ := Prod.fst <$> answer
def ans₂ := Prod.snd <$> answer
