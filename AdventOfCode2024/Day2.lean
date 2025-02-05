import AdventOfCode2024.Basic

def lines := load "AdventOfCode2024/Inputs/Day2.txt"

def data :=
  lines >>= List.mapM fun line => line.splitOn.mapM (monadLift ∘ String.toNat?')

inductive Safety
| safe: Ordering → Safety
| «unsafe»

def Safety.isSafe: Safety → Bool
| .safe _ => true
| .unsafe => false

instance : Repr Safety where
  reprPrec := fun s _ => match s with
  | .safe .lt => "<"
  | .safe .eq => "="
  | .safe .gt => ">"
  | .unsafe => "unsafe"

instance : ToString Ordering where
  toString
  | .lt => "<"
  | .eq => "="
  | .gt => ">"

instance : ToString Safety where
  toString s := (instReprSafety.reprPrec s 0).pretty

def process (soFar: Ordering): List Nat → Safety
| [] => .safe soFar
| [_] => .safe soFar
| x :: y :: rest =>
  let safetyXY: Safety := match soFar with
  | .lt =>
    if x < y && y - x <= 3 then .safe .lt else .unsafe
  | .eq =>
    if x < y && y - x <= 3 then .safe .lt
    else if x > y && x - y <= 3 then .safe .gt
    else .unsafe
  | .gt =>
    if x > y && x - y <= 3 then .safe .gt else .unsafe

  match safetyXY with
  | .safe o => process o (y :: rest)
  | .unsafe => .unsafe

def ans₁: IO Nat :=
  data >>= (fun data =>
    data
      |>.map (process .eq)
      |>.filter Safety.isSafe
      |>.length
      |> pure)

def List.removeOne (l: List α) :=
  (List.range l.length).map l.eraseIdx

def ans₂: IO Nat :=
  data >>= (fun data =>
    data
      |>.filter (fun reactor =>
        (process .eq reactor).isSafe
        || reactor.removeOne.any (process .eq · |>.isSafe))
      |>.length
      |> pure)

#eval ans₁
#eval ans₂
