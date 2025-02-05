import AdventOfCode2024.Basic

def data := load "AdventOfCode2024/Inputs/Day22.txt"
  >>= fun lines => monadLift <| lines.mapM (String.toNat?')

@[inline]
def mix := UInt32.xor

@[inline]
def prune (x: UInt32): UInt32 := x &&& 0xffffff

@[inline]
def next: UInt32 → UInt32
| n =>
  let n := prune (mix (n * 64) n) -- first step
  let n := prune (mix (n / 32) n) -- second step
  let n := prune (mix (n * 2048) n) -- third step
  n

def initialSecrets :=
  List.map Nat.toUInt32 <$> data

def ans₁ :=
  List.sum <$>
  List.map (fun x => Function.repeat next x 2000) <$>
  initialSecrets

def allSecrets (n: ℕ) (seed: UInt32) :=
  (go seed [] n).reverse
where
  go secret acc: ℕ → List UInt32
  | 0 => acc
  | k + 1 =>
    let secret' := next secret
    go secret' (secret' :: acc) k

abbrev Key := Int32 × Int32 × Int32 × Int32

instance : ToString Key where
  toString
  | (x₁, x₂, x₃, x₄) =>
    s!"({x₁}, {x₂}, {x₃}, {x₄})"

instance : Hashable Int32 where
  hash := hash ∘ Int32.toUInt32

def getPriceChanges: List UInt32 → Std.HashMap Key ℕ
| x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: rest =>
  go
    (Int32.sub ⟨x₂⟩ ⟨x₁⟩,
     Int32.sub ⟨x₃⟩ ⟨x₂⟩,
     Int32.sub ⟨x₄⟩ ⟨x₃⟩,
     Int32.sub ⟨x₅⟩ ⟨x₄⟩)
    x₅
    {}
    rest
| _ => {}
where
  go key price (acc: Std.HashMap Key ℕ) (rest: List UInt32): Std.HashMap Key ℕ :=
    -- dbg_trace "{key} {price} {acc.toList} {rest}"
    let (_, d₂, d₃, d₄) := key
    let nextMap := acc.insertIfNew key price.toNat
    match rest with
    | [] => nextMap
    | x :: xs => go (d₂, d₃, d₄, Int32.sub ⟨x⟩ ⟨price⟩) x nextMap xs

-- Like union (traverse over `m₂`) but sum values
def addUnion (m₁ m₂: Std.HashMap Key ℕ) := Id.run do
  let mut m₁ := m₁
  for (k, v) in m₂ do
    let v' :=
      if h: k ∈ m₁ then
        v + m₁.get k h
      else
        v
    m₁ := m₁.insert k v'

  return m₁

def ans₂: IO ℕ := do
  let map := (←initialSecrets)
    |>.map (fun seed => seed :: allSecrets 2000 seed)
    |>.map (List.map (· % 10))
    |>.map getPriceChanges
    |>.foldr (fun s acc => addUnion acc s) {}
  return map.values.max?.get!
