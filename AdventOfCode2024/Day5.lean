import AdventOfCode2024.Basic

def input := loadAsString "AdventOfCode2024/Inputs/Day5.txt"

abbrev OddLengthList α := { l: List α // l.length % 2 = 1 }

def rulesAndPages: IO (List (ℕ × ℕ) × List (OddLengthList ℕ)) := do
  let str ← input
  let [rulesStr, pagesStr] := str.splitOn "\n\n"
    | .error s!"Could not split `{str}` into two!"
  let rules ← (rulesStr.splitOn "\n").mapM fun line => do
    let [aStr, bStr] := line.splitOn "|"
      | .error s!"Could not split `{line}` into two `String`s!"
    return (←aStr.toNat?', ←bStr.toNat?')
  let pages ← (pagesStr.splitOn "\n").mapM fun line => do
    let lst ← (line.splitOn ",").mapM (liftM ∘ String.toNat?')
    if h: lst.length % 2 = 1 then
      return ⟨lst, h⟩
    else
      .error s!"Even length: {lst}"

  return (rules, pages)

def pagesInOrder (rules: Std.HashSet (ℕ × ℕ)) (pages: List ℕ): List ℕ :=
  pages.mergeSort fun x y => (x, y) ∈ rules

@[inline]
def OddLengthList.middle: OddLengthList α → α
| ⟨lst, _⟩ => lst[lst.length / 2]

def ans₁: IO ℕ := do
  let (rules, pages) ← rulesAndPages
  let rulesSet := Std.HashSet.ofList rules
  return pages
    |>.filter (fun ⟨lst, _⟩ => lst = pagesInOrder rulesSet lst)
    |>.map OddLengthList.middle
    |>.sum

#eval ans₁

def ans₂: IO ℕ := do
  let (rules, pages) ← rulesAndPages
  let rulesSet := Std.HashSet.ofList rules
  return pages
    |>.filterMap (fun ⟨lst, _⟩ =>
      let ordered := pagesInOrder rulesSet lst
      if lst = ordered then
        none
      else
        some ⟨ordered, by simpa [ordered, pagesInOrder]⟩)
    |>.map OddLengthList.middle
    |>.sum

#eval ans₂
