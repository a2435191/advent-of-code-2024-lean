import AdventOfCode2024.Basic

def input := loadAsString "AdventOfCode2024/Inputs/Day17.txt"

structure Combo where
  n: Fin 7
deriving Repr

def Combo.ofNat (n: ℕ): Except String Combo :=
  if h: n < 7 then .ok ⟨n, h⟩
  else .error s!"Combo requires n < 7, but n = {n}"

structure Literal where
  n: Fin 8
deriving Repr

def Literal.ofNat (n: ℕ): Except String Literal :=
  if h: n < 8 then .ok ⟨n, h⟩
  else .error s!"Combo requires n < 8, but n = {n}"

inductive Instruction
| adv: Combo → Instruction
| bxl: Literal → Instruction
| bst: Combo → Instruction
| jnz: Literal → Instruction
| bxc
| out: Combo → Instruction
| bdv: Combo → Instruction
| cdv: Combo → Instruction

instance : ToString Instruction where
  toString
  | .adv ⟨i⟩ => s!"adv {i}"
  | .bxl ⟨i⟩ => s!"bxl {i}"
  | .bst ⟨i⟩ => s!"bst {i}"
  | .jnz ⟨i⟩ => s!"jnz {i}"
  | .bxc     =>   "bxc"
  | .out ⟨i⟩ => s!"out {i}"
  | .bdv ⟨i⟩ => s!"bdv {i}"
  | .cdv ⟨i⟩ => s!"cdv {i}"

instance : Repr Instruction := ⟨fun instr _ => toString instr⟩

def Instruction.ofNats (instr operand: ℕ): Except String Instruction := do
  match instr with
  | 0 => return .adv (←Combo.ofNat operand)
  | 1 => return .bxl (←Literal.ofNat operand)
  | 2 => return .bst (←Combo.ofNat operand)
  | 3 => return .jnz (←Literal.ofNat operand)
  | 4 => return .bxc
  | 5 => return .out (←Combo.ofNat operand)
  | 6 => return .bdv (←Combo.ofNat operand)
  | 7 => return .cdv (←Combo.ofNat operand)
  | _ => .error s!"No instruction corresponding to `{instr}`"

structure Registers where
  a: ℕ
  b: ℕ
  c: ℕ
deriving Repr

@[inline]
def Registers.evalCombo (reg: Registers): Combo → ℕ
| .mk 0 => 0
| .mk 1 => 1
| .mk 2 => 2
| .mk 3 => 3
| .mk 4 => reg.a
| .mk 5 => reg.b
| .mk 6 => reg.c

structure Program where
  instructions: Array Instruction
  registers: Registers
  ip: Fin instructions.size
deriving Repr

/-- Return updated registers, IP, output. -/
def Program.step: (p: Program) → Registers × Option (Fin p.instructions.size) × Option ℕ
| ⟨instructions, regs@⟨a, b, c⟩, ip⟩ =>
  let instr := instructions[ip]
  let nextIPLocation: ℕ := match instr with
    | .jnz ⟨n⟩ => if a = 0 then ip + 2 else n
    | _ => ip + 1
  let nextIP :=
    if h: nextIPLocation < instructions.size then
      some ⟨nextIPLocation, h⟩
    else none

  let output := match instr with
    | .out arg => some <| (regs.evalCombo arg) % 8
    | _ => none

  let nextRegs := match instr with
    | .adv arg => { regs with a := regs.a >>> regs.evalCombo arg }
    | .bdv arg => { regs with b := regs.a >>> regs.evalCombo arg }
    | .cdv arg => { regs with c := regs.a >>> regs.evalCombo arg }
    | .bxl ⟨n⟩ => { regs with b := regs.b ^^^ n }
    | .bst arg => { regs with b := (regs.evalCombo arg) % 8 }
    | .jnz ⟨n⟩ => regs
    | .bxc =>     { regs with b := regs.b ^^^ regs.c }
    | .out arg => regs


  ⟨nextRegs, nextIP, output⟩

def registersAndInstructionCodes (str: String): Except String (Registers × List ℕ) := do
  let [registersStr, programStr] := str.splitOn "\n\n"
    | .error s!"Could not split `{str}`"
  let registers: List ℕ ← registersStr
    |>.splitOn "\n"
    |>.mapM fun s => do
      let some suffix :=
        s.dropPrefix? "Register A: " <|>
        s.dropPrefix? "Register B: " <|>
        s.dropPrefix? "Register C: "
        | .error s!"Could not find `Register _: ` prefix for `{s}`"
      suffix.toString.toNat?'
  let [a, b, c] := registers
    | .error s!"registers `{registers}` should have length 3"

  let some programStrSuffix := programStr.dropPrefix? "Program: "
    | .error s!"Could not find `Program: ` prefix for `{programStr}`"

  let instructionCodes: List ℕ := ←programStrSuffix
    |>.splitOn ","
    |>.mapM (fun s => s.toString.toNat?')

  return ({ a, b, c }, instructionCodes)

def Instruction.ofCodes (instructionCodes: List ℕ): Except String (Array Instruction) :=
  instructionCodes
    |>.toChunks 2
    |>.mapM (fun
      | [instrN, operandN] => Instruction.ofNats instrN operandN
      | l => .error s!"Expected the instructions list to have even \
                      length, but cannot form a pair from `{l}`")
    |> Functor.map List.toArray

@[simp]
lemma Array.size_pos_of_not_isEmpty (h: ¬(Array.isEmpty a)): a.size > 0 :=
  Array.size_pos.mpr (fun hn => by simp [hn] at h)

def Program.run: Program → Registers × List ℕ × ℕ
| ⟨instructions, initialRegisters, initialIP⟩ => Id.run do
  let mut registers := initialRegisters
  let mut ip := initialIP
  let mut out := []
  let mut i := 0
  while true do
    let (nextRegs, nextIP, optionOutput) := Program.step ⟨instructions, registers, ip⟩
    registers := nextRegs
    if let some n := optionOutput then
      out := n :: out
    if let some ip' := nextIP then
      ip := ip'
      i := i + 1
    else
      break
  return (registers, out.reverse, i)

def ans₁: IO String := do
  let (registers, codes) ← registersAndInstructionCodes (←input)
  let instructions ← Instruction.ofCodes codes
  if h: instructions.isEmpty then
    .error "No instructions"
  else
    let program := Program.mk
      instructions
      registers
      ⟨0, Array.size_pos_of_not_isEmpty h⟩
    let (_, output, _) := program.run
    return String.intercalate "," (output.map toString)

/-- Returns a predicate on `a`: whether the program outputs
    its own instructions when `A = a` and `B = C = 0`.-/
partial def isQuine (instructionCodes: List ℕ): Except String (ℕ → Bool) := do
  let instructions ← Instruction.ofCodes instructionCodes
  if h: instructions.isEmpty then
    .error "Empty instructions"
  else
    .ok fun a =>
      let program := Program.mk
        instructions
        ⟨a, 0, 0⟩
        ⟨0, Array.size_pos_of_not_isEmpty h⟩

      -- more efficient way of calculating `program.run.2.1 = instructionCodes`
      go program instructionCodes
where
  go (program: Program) (remaining: List ℕ): Bool :=
    let (nextRegisters, nextIP, optionOutput) := program.step
    match remaining with
    | [] =>
      match optionOutput, nextIP with
      | some _, _ => false
      | none, none => true
      | none, some ip => go { program with ip, registers := nextRegisters } []
    | x :: xs =>
      match optionOutput, nextIP with
      | none, none => false
      | some n, none => x = n && xs.isEmpty
      | some n, some ip => x = n && go { program with ip, registers := nextRegisters } xs
      | none, some ip => go { program with ip, registers := nextRegisters } (x :: xs)

/-  Compute possible values of `a` to run `Program.isQuine` on.
    Assumes the program is the following:
    1 - bst 4 # B ← A % 8
    2 - bxl 6 # B ← B xor 0b110
    3 - cdv 5 # C ← A >> B
    4 - bxc   # B ← B xor C
    5 - bxl 7 # B ← B xor 0b111 (flip all the bits)
    6 - adv 3 # A ← A / 8
    7 - out 5 # output B % 8
    8 - jnz 0 # if A = 0, terminate. Otherwise go back to line 1

    The last number is `0`. So `B₅` (after line 5) must be `0`.
    On the last loop iteration, `A₆ = 0`, so `A₀ < 8`. The only such value
    of `A₀` that has `B₅ = 0` is `A₀ = 1`. Equivalently, `a >> (3 * (x - 1)) = 1`.
    Thus, we only have to search in `[2^45, 2^46)`.

    The second-to-last number is `3` (`jnz`). We also know that in the second-to-last
    iteration, `A₆ = 1` (the `A₀` for the last iteration). Therefore, `8 ≤ A₀ < 15`.
    The only such value that has `B₅ = 3` is `A₀ = 10`. Equivalently, `a >> (3 * (x - 2)) = 10`.
    Thus, we only have to search in `[10 * 2^42, 11 * 2^42)`.

    The third-to-last number is `5`. We must have `A₆ = 10`, so `80 ≤ A₀ < 88`. To get `B₅ = 5`, we need
    `A₀ = 87`. Equivalently, `a >> (3 * (x - 3)) = 87`. We can narrow the search to
    `[87 * 2^39, 88 * 2^39)`.

    For the fourth-to-last number, `A₆ = 87`, so `696 ≤ A₀ < 704`. We need `B₅ = 5` (`out`), so
    `A₀ = 697`. Therefore, `a ∈ [697 * 2^36, 698 * 2^36)`.

    For the fifth-to-last number, `A₆ = 697`, so `5,576 ≤ A₀ < 5,584`. We need `B₅ = 3`, so
    `A₀ = 5,577`. Therefore, `a ∈ [5,577 * 2^33, 5,578 * 2^33)`.

    For the sixth-to-last number, `A₆ = 5,577`, so `44,616 ≤ A₀ < 44,624`. We need `B₅ = 0` (`adv`), so
    `A₀ ∈ { 44616, 44619 }`. There are two solutions. Hence,
    `a ∈ [44,616 * 2^30, 44,617 * 2^30) ∪ [44,619 * 2^30, 44,620 * 2^30)`.

    For the seventh-to-last number, `A₆ = 44,616` or `44,619`. We need `B₅ = 7`, so
    `A₀ ∈ { 356,930, 356,957 }`. Hence,
    `a ∈ [356,930 * 2^27, 356,931 * 2^27) ∪ [356,957 * 2^27, 356,958 * 2^27)`.

    We repeat this process for the entire input list, and by the end the exponents are `0`, so the
    search ranges are of the form `[x, x + 1)`. Thus, we just return the `x`s.
    Note that the head of the input list should represent the last number in the instruction sequence.
    -/
def findQuineInputCandidates (targets: List ℕ): List ℕ :=
  go 0 targets
where
  /-- returns the list of A₀'s that give B₅ the correct value,
      given the target A₆ value -/
  go (a₆: ℕ): List ℕ → List ℕ
  | [] => [a₆]
  | target :: rest =>
    -- dbg_trace s!"{a₆} {target} {rest}"
    let computeOutputValue (a₀: ℕ): ℕ :=
      let b := a₀ % 8
      let b := b ^^^ 0b110
      let c := a₀ >>> b
      let b := b ^^^ c
      let b := b ^^^ 0b111
      b % 8
    let a₀s := List.range' (8 * a₆) 8
      |>.filter (computeOutputValue · = target)
    -- dbg_trace s!"a₀s: {a₀s}"
    a₀s
      |>.map (fun a₀ => go a₀ rest)
      |>.flatten

def ans₂: IO ℕ := do
  let (_, codes) ← registersAndInstructionCodes (←input)
  let quinePred ← isQuine codes
  let some a := findQuineInputCandidates codes.reverse
    |>.filter quinePred
    |>.min?
    | .error "No minimum `a` value exists"
  return a
