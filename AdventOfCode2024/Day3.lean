import AdventOfCode2024.Basic

def data := loadAsString "AdventOfCode2024/Inputs/Day3.txt"

partial def evalMuls (acc: Nat) (s: Substring) := Id.run do
  if s.isEmpty then
    return acc
  match s.dropPrefix? "mul(".toSubstring with
  | .none => evalMuls acc (s.drop 1)
  | .some rest =>
    let xString := rest.takeWhile Char.isDigit
    unless xString.isNat do
      return ←evalMuls acc rest
    let rest := rest.drop xString.bsize
    unless rest.front = ',' do
      return ←evalMuls acc rest
    let rest := rest.drop 1
    let yString := rest.takeWhile Char.isDigit
    unless yString.isNat do
      return ←evalMuls acc rest
    let rest := rest.drop yString.bsize
    unless rest.front = ')' do
      return ←evalMuls acc rest
    --dbg_trace "{acc} {s.bsize} {xString} {yString}";
    return ←evalMuls (acc + xString.toNat?.get! * yString.toNat?.get!) (rest.drop 1)

def ans₁ := (evalMuls 0 ·.toSubstring) <$> data

partial def evalMulsDoAndDont (acc: Nat) (enabled: Bool) (s: Substring) := Id.run do
  if s.isEmpty then
    return acc
  if enabled then
    match s.dropPrefix? "don't()".toSubstring with
    | .some rest => evalMulsDoAndDont acc false rest
    | .none =>
      match s.dropPrefix? "mul(".toSubstring with
      | .none => evalMulsDoAndDont acc enabled (s.drop 1)
      | .some rest =>
        let xString := rest.takeWhile Char.isDigit
        unless xString.isNat do
          return ←evalMulsDoAndDont acc enabled rest
        let rest := rest.drop xString.bsize
        unless rest.front = ',' do
          return ←evalMulsDoAndDont acc enabled rest
        let rest := rest.drop 1
        let yString := rest.takeWhile Char.isDigit
        unless yString.isNat do
          return ←evalMulsDoAndDont acc enabled rest
        let rest := rest.drop yString.bsize
        unless rest.front = ')' do
          return ←evalMulsDoAndDont acc enabled rest
        --dbg_trace "{acc} {s.bsize} {xString} {yString}";
        return ←evalMulsDoAndDont (acc + xString.toNat?.get! * yString.toNat?.get!) enabled (rest.drop 1)
  else
    match s.dropPrefix? "do()".toSubstring with
    | .none => evalMulsDoAndDont acc false (s.drop 1)
    | .some rest => evalMulsDoAndDont acc true rest


def ans₂ := (evalMulsDoAndDont 0 true ·.toSubstring) <$> data
