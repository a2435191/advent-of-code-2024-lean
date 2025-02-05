import AdventOfCode2024.Basic
def input := loadAsString "AdventOfCode2024/Inputs/Day11.txt"

def stones: IO (List ℕ) := do
  (←input)
    |>.splitOn " "
    |>.mapM (monadLift ∘ String.toNat?')

open Lean.MonadHashMapCacheAdapter in
def countStones (initStone blinks: ℕ): Lean.MonadStateCacheT (ℕ × ℕ) ℕ Id ℕ := do
  if let some cached ← findCached? (initStone, blinks) then
    return cached
  let res ←
    match initStone, blinks with
    | _, 0 => return 1
    | 0, k + 1 => countStones 1 k
    | n, k + 1 =>
      let str := toString n
      if str.length % 2 = 0 then
        let m := str.length / 2
        countStones (n % 10^m) k >>= fun r =>
        countStones (n / 10^m) k >>= fun l =>
        return l + r
      else
        countStones (2024 * n) k

  cache (initStone, blinks) res
  return res

def lengthAfterBlinks (initStones: List ℕ) (blinks: ℕ) := Id.run do
  let mut acc := 0
  let mut cache := {}
  for initStone in initStones do
    let res := StateT.run (countStones initStone blinks) {}
    acc := acc + res.fst
    cache := res.snd
  return acc

def ans₁ :=
  return lengthAfterBlinks (←stones) 25

-- #eval ans₁

def ans₂ :=
  return lengthAfterBlinks (←stones) 75

-- #eval ans₂
