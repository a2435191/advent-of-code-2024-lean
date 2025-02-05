import AdventOfCode2024.Basic

def lines := load "AdventOfCode2024/Inputs/Day1.txt"

def data: ExceptT String IO (List (Nat × Nat)) :=
  lines >>= List.mapM fun line => do
    match line.splitOn "   " with
    | [l, r] =>
      let a ← l.toNat?'
      let b ← r.toNat?'
      return (a, b)
    | _ => throw (s!"line `{line}` could not be split into two")

def ans₁: IO Nat :=
  data.map (fun l =>
    let (xs, ys) := l.unzip
    let zipped := List.zip xs.mergeSort ys.mergeSort
    zipped
      |>.map (fun (x, y) => Int.natAbs (Int.sub (Int.ofNat x) (Int.ofNat y)))
      |>.sum)
  >>= monadLift


def ans₂: IO Nat :=
  data.map (fun l =>
    let (xs, ys) := l.unzip
    xs
      |>.map (fun x => x * ys.count x)
      |>.sum)
  >>= monadLift


#eval ans₁
#eval ans₂
