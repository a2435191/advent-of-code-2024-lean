import AdventOfCode2024.Basic
import Mathlib.Data.Nat.Digits

def input := load "AdventOfCode2024/Inputs/Day7.txt"

def calibrationEquations: IO (List (ℕ × List ℕ)) :=
  input >>= List.mapM fun line => do
    let [testValueStr, numsStr] := line.splitOn ": "
      | .error s!"Could not parse line {line} into two parts"
    let testValue ← testValueStr.toNat?'
    let nums ← numsStr.splitOn.mapM (liftM ∘ String.toNat?')
    if 0 ∈ nums then .error s!"0 ∈ {nums}" -- needed for the ≤ necessary condition
    return (testValue, nums)

@[specialize]
def canMakeEquationTrue (useConcat: Bool) (testValue: ℕ): List ℕ → Bool
| [] => false -- like NaN
| x :: xs => go x xs
where
  go curr
  | [] => curr = testValue
  | n :: rest =>
    -- bound with the ≤ necessary condition
    (curr + n ≤ testValue && go (curr + n) rest)
    || (curr * n ≤ testValue && go (curr * n) rest)
    || (useConcat &&
      let concatted := Nat.ofDigits 10 <| (Nat.digits 10 n) ++ (Nat.digits 10 curr)
      concatted ≤ testValue && go concatted rest)

def calibrationResult (useConcat: Bool): IO ℕ := do
  let eqns ← calibrationEquations
  let possibleEqns := eqns.filter fun (testValue, nums) =>
    canMakeEquationTrue useConcat testValue nums
  return (possibleEqns.map Prod.fst).sum

def ans₁ :=
  calibrationResult false

def ans₂ :=
  calibrationResult true

#eval ans₂
