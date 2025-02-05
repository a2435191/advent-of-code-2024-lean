import AdventOfCode2024.Basic

def input := load' "AdventOfCode2024/Inputs/Day13.txt"

structure ClawMachine where
  aX: ℕ
  aY: ℕ
  bX: ℕ
  bY: ℕ
  prizeX: ℕ
  prizeY: ℕ
deriving Repr

def clawMachines: IO (List (ClawMachine)) := do
  (←input).mapM fun clawMachineString => do
    let [aString, bString, prizeString] := clawMachineString.splitOn "\n"
      | .error s!"Could not split `{clawMachineString}` into three parts"
    let parseXY («prefix»: String) (between: String) str := do
      let suffix ← String.dropPrefix? str «prefix»
        |>.toExcept s!"`{str}` does not start with `{«prefix»}`"
      let [xString, yString] := suffix.splitOn ", "
        | .error s!"Could not split `{suffix}`"
      let x ← xString.dropPrefix? ("X" ++ between)
        |>.toExcept s!"`{xString}` does not start with `X{between}`"
        |>.map Substring.toString
        |>.bind String.toNat?'
      let y ← yString.dropPrefix? ("Y" ++ between)
        |>.toExcept s!"`{yString}` does not start with `Y{between}`"
        |>.map Substring.toString
        |>.bind String.toNat?'
      return (x, y)
    let (aX, aY) ← parseXY "Button A: " "+" aString
    let (bX, bY) ← parseXY "Button B: " "+" bString
    let (prizeX, prizeY) ← parseXY "Prize: " "=" prizeString
    return { aX, aY, bX, bY, prizeX, prizeY }

/-- Returns `(a, b)` if such a solution exists-/
def ClawMachine.solve (cm: ClawMachine): Option (ℕ × ℕ) := do
  /- We solve
    [ aX bX  [ a   = [ prizeX
      aY bY ]  b ]     prizeY ]
  -/
  let { aX, aY, bX, bY, prizeX, prizeY } := cm
  let denominator := Int.sub (aX * bY) (aY * bX)

  let a := (Int.sub (bY * prizeX) (bX * prizeY)) / denominator
  let b := (Int.sub (aX * prizeY) (aY * prizeX)) / denominator

  -- dbg_trace s!"{a} {b}"
  /- in addition to the matrix inverse existing, we also want solutions
     *in ℕ²*. -/
  let a' ← a.toNat'
  let b' ← b.toNat'

  if aX * a' + bX * b' = prizeX && aY * a' + bY * b' = prizeY then
    return (a', b')
  else none

def tokens: ℕ × ℕ → ℕ
| (a, b) => 3 * a + b

def ans₁: IO ℕ := do
  let tokensList ← (←clawMachines)
    |>.filterMap ClawMachine.solve
    |>.filterM (fun (a, b) => do
      if a ≤ 100 && b ≤ 100 then
        return true
      .error s!"Solution `{(a, b)}` takes more \
              than `100` presses per button")
  return (tokensList.map tokens).sum
def ans₂: IO ℕ := do
  let offset := 10000000000000
  let tokensList := (←clawMachines)
    |>.map (fun cm => { cm with
                        prizeX := cm.prizeX + offset,
                        prizeY := cm.prizeY + offset })
    |>.filterMap ClawMachine.solve
  return (tokensList.map tokens).sum

#eval ans₂
