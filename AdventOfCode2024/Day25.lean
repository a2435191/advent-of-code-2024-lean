import AdventOfCode2024.Basic

def input := loadAsString "AdventOfCode2024/Inputs/Day25.txt"

structure Key where
  heights: List ℕ
deriving Repr

structure Lock where
  heights: List ℕ
deriving Repr

def heights: List String → List ℕ
| [] => []
| s :: rest =>
  let currentHeights := s.toList.map (if · = '#' then 1 else 0)
  match rest with
  | [] => currentHeights
  | _ => List.zipWith Nat.add currentHeights (heights rest)


def parseInput: IO (List Key × List Lock × ℕ × ℕ) := do
  let (keyStrings, lockStrings) ← (←input)
    |>.splitOn "\n\n"
    |>.map (String.splitOn (sep := "\n"))
    |>.partitionM fun s =>
      match h: s with
      | [] => .error "No first row found"
      | hd :: _ =>
        if hd.all (· = '.') ∧ (s.getLast (by simp [h])).all (· = '#') then .ok true
        else if hd.all (· = '#') ∧ (s.getLast (by simp [h])).all (· = '.') then .ok false
        else .error s!"First and last row of `{s}` do not consist of \
                      all `.` or `#` characters, respectively, or vice versa"

  let keys := keyStrings.map (Key.mk ∘ List.map (· - 1) ∘ heights)
  let locks := lockStrings.map (Lock.mk ∘ List.map (· - 1) ∘ heights)
  let width := (keyStrings.head? >>= List.head?) <&> String.length |>.getD 0
  let height := List.length <$> keyStrings.head? |>.getD 0
  return (keys, locks, width, height - 2) -- -2 because we don't count top or bottom row

def fit (key: Key) (lock: Lock) (maxHeight: ℕ) :=
  List.all₂ (· + · ≤ maxHeight) key.heights lock.heights

def ans₁: IO ℕ := do
  let (keys, locks, _, height) ← parseInput
  return List.product keys locks
    |>.countP fun (k, l) => fit k l height

#eval ans₁
