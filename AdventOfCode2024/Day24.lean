import AdventOfCode2024.Basic
import Mathlib.Data.Nat.Digits

def input := loadAsString "AdventOfCode2024/Inputs/Day24.txt"

inductive Gate
| and: Gate → Gate → Gate
| or:  Gate → Gate → Gate
| xor: Gate → Gate → Gate
| var: String → Gate
| literal: Bool → Gate
deriving Repr, DecidableEq, Inhabited

def parseGates: IO (Std.HashMap String Gate × Std.HashMap String Gate) := do
  let inputStr ← input
  let [wiresStr, gatesStr] := inputStr.splitOn "\n\n"
    | throw <| .userError s!"Could not parse wires and gates from `{inputStr}`"
  let wires: List (String × Gate) ← wiresStr
    |>.splitOn "\n"
    |>.mapM (fun line =>
      match String.splitOn line ": " with
      | [wire, "1"] => return (wire, .literal true)
      | [wire, "0"] => return (wire, .literal false)
      | _ => throw <| .userError s!"Could not parse initial wire configuration from `{line}`")

  let gates: List (String × Gate) ← gatesStr
    |>.splitOn "\n"
    |>.mapM (fun line =>
      match String.splitOn line with
      | [x, "AND", y, "->", res] => return (res, .and (.var x) (.var y))
      | [x, "OR",  y, "->", res] => return (res, .or  (.var x) (.var y))
      | [x, "XOR", y, "->", res] => return (res, .xor (.var x) (.var y))
      | _ => throw <| .userError s!"Could not parse gate from `{line}`")

  return (.ofList wires, .ofList gates)

partial def Gate.eval (mapping: Std.HashMap String Gate) (g: Gate) (depth: Option ℕ := none): Gate :=
  if depth = some 0 then g
  else
    let nextDepth := Nat.pred <$> depth
    match g with
    | .literal b => .literal b
    | .var s =>
      match mapping.get? s with
      | none => .var s
      | some g => eval mapping g depth
    | .and l r =>
      let l' := eval mapping l nextDepth
      let r' := eval mapping r nextDepth
      match l', r' with
      | .literal bl, .literal br => .literal (bl && br)
      | _, _ => .and l' r'
    | .xor l r =>
      let l' := eval mapping l nextDepth
      let r' := eval mapping r nextDepth
      match l', r' with
      | .literal bl, .literal br => .literal (Bool.xor bl br)
      | _, _ => .xor l' r'
    | .or l r =>
      let l' := eval mapping l nextDepth
      let r' := eval mapping r nextDepth
      match l', r' with
      | .literal bl, .literal br => .literal (bl || br)
      | _, _ => .or  l' r'

def Gate.zs (mapping: Std.HashMap String Gate): Except String (List Gate) := do
  let zs ← mapping
    |>.filter (fun name _ => name.startsWith "z")
    |>.toList
    |>.mapM (fun (name, g) => (·, g) <$> (name.drop 1).toNat?')
    |> Functor.map (List.mergeSort (le := fun (i, _) (j, _) => i ≤ j))

  let (indices, _) := zs.unzip
  if indices ≠ List.range zs.length then
    throw s!"some indices missing from {repr zs}"
  return zs.map Prod.snd

def Gate.toNat (mapping: Std.HashMap String Gate): Except String ℕ := do
  let zs ← Gate.zs mapping
  let bits ← zs
    |>.map (eval mapping)
    |>.mapM (fun
      | .literal b => return b
      | other => throw s!"{repr other} has unbound variables")
  return Nat.ofDigits 2 (bits.map Bool.toNat)

def wiresOfList (bits: List (ℕ × Bool)) (pref: String): Std.HashMap String Gate :=
  let length := s!"{bits.length - 1}".length
  bits
    |>.map (fun (i, b) =>
      let str := pref ++ String.leftpad length '0' (toString i)
      (str, .literal b))
    |> Std.HashMap.ofList

def makeKey (pre: String) (x: ℕ) :=
  pre ++ (toString x).leftpad 2 '0'

def wiresOfStrings (x y: String): Except String (Std.HashMap String Gate) := do
  let getBits (s: String): Except String (List Bool) :=
    s.toList.filterMapM fun
    | '0' => return some false
    | '1' => return some true
    | '_' => return none
    | c => throw s!"Character `{c}` in string `{s}` is not `0` or `1` or `_`"
  let xWires := wiresOfList (←getBits x).enum "x"
  let yWires := wiresOfList (←getBits y).enum "y"
  return xWires ∪ yWires

def getCarryBit (gates: Std.HashMap String Gate): ℕ → Except String Gate
| 0 => .ok (.literal false)
| k + 1 =>
  let key := makeKey "z" (k + 1)
  match Gate.eval gates (.var key) (some 2) with
  | .xor (.xor _ _) C
  | .xor C (.xor _ _) => .ok C
  | z => .error s!"Tried getting key `{key}`, but could \
    not find carry bit value in {repr z}; expected \
    XOR (XOR (...), C) or XOR (C, XOR (...))."

/-- All XOR gates must either output into a zᵢ variable or take in xᵢ, yᵢ -/
def validateXORs (gates: Std.HashMap String Gate): List String :=
  gates
    |>.toList
    |>.filterMap fun (k, v) =>
      if k.startsWith "z" then none
      else match v with
        | .xor (.var s₁) (.var s₂) =>
          if (s₁.startsWith "x" ∧ s₂.startsWith "y")
           ∨ (s₁.startsWith "y" ∧ s₂.startsWith "x") then none
          else k
        | .xor _ _ => k
        | _ => none


def expectedCarryBit (prevIndex: ℕ) (prevCarry: Gate): Gate :=
  let x := .var (makeKey "x" (prevIndex + 1))
  let y := .var (makeKey "y" (prevIndex + 1))
  let xPrev := .var (makeKey "x" prevIndex)
  let yPrev := .var (makeKey "y" prevIndex)
  match prevIndex with
  | 0 => -- the 1 case short-circuits part of the right branch,
         -- because the 0th carry bit is always `false`
    .xor (.xor x y) (.and xPrev yPrev)
  | _ =>
    .xor
      (.xor x y)
      (.or
        (.and xPrev yPrev)
        (.and
          prevCarry
          (.xor xPrev yPrev)))

def ans₁: IO ℕ :=
  parseGates >>= fun (wires, gates) =>
    Gate.toNat (wires ∪ gates)

#eval ans₁

def Std.HashMap.swap [BEq α] [Hashable α] (map: Std.HashMap α β) (k₁ k₂: α): Except α (Std.HashMap α β) := do
  let v₁ ← match map[k₁]? with
    | some v => .ok v
    | none => .error k₁
  let v₂ ← match map[k₂]? with
    | some v => .ok v
    | none => .error k₂
  return map
    |>.insert k₁ v₂
    |>.insert k₂ v₁


def toBinaryString (width: ℕ) (n: ℕ): String :=
  Nat.bits n
    |>.map Bool.toNat
    |>.map toString
    |> String.join
    |>.rightpad width '0'

def ans₂: IO String := do
  let (wires, gates) ← parseGates
  let n := wires.size / 2
  let swaps := [
    ("fkp", "z06"),
    ("ngr", "z11"),
    ("mfm", "z31"),
    ("krj", "bpt")]
  have: swaps.length = 4 := rfl
  let swappedGates ← swaps
    |>.foldrM (fun (k₁, k₂) dict => dict.swap k₁ k₂) gates

  for i in [0 : n] do
    let carry := getCarryBit swappedGates i
    match carry with
    | .error s =>
      IO.eprintln s!"{i} {s}"
    | .ok _ => pure ()

  return swaps
    |>.map (fun (k₁, k₂) => [k₁, k₂])
    |>.flatten
    |>.mergeSort
    |> String.intercalate ","

#eval ans₂
