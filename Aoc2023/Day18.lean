import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day18

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_18_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_18_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_18"

/-
PART 1:
-/

inductive Direction
| n | w | e | s
deriving BEq, Repr, Inhabited

instance : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"

def stepsDir (pos : Int × Int) (dir : Direction) (steps : Int) : Int × Int :=
  match dir with
  | .n => ⟨pos.1 - steps, pos.2⟩
  | .w => ⟨pos.1, pos.2 - steps⟩
  | .s => ⟨pos.1 + steps, pos.2⟩
  | .e => ⟨pos.1, pos.2 + steps⟩

def parseLine₁ : Parsec (Direction × Nat) := do
  let c ← anyChar
  ws
  let n ← natNum
  ws
  let _ ← pstring "(#"
  let _ ← many1 alphanum
  let _ ← pchar ')'
  match c with
  | 'R' => return ⟨.e, n⟩
  | 'L' => return ⟨.w, n⟩
  | 'U' => return ⟨.n, n⟩
  | 'D' => return ⟨.s, n⟩
  | _ => fail "Parse error"

def turningRight (dir₁ dir₂ : Direction) : Bool :=
  match dir₁, dir₂ with
  | .n, .e => true
  | .s, .w => true
  | .e, .s => true
  | .w, .n => true
  | _, _ => false

def turningLeft (dir₁ dir₂ : Direction) : Bool :=
  match dir₁, dir₂ with
  | .n, .w => true
  | .s, .e => true
  | .e, .n => true
  | .w, .s => true
  | _, _ => false

-- Walk the path with the "cursor" at the front right
def walkRight (ins : Array (Direction × Nat)) : Int := Id.run do
  let numinst := ins.size
  let mut pos : Int × Int := ⟨0, 0⟩
  let mut out : Int := 0
  for i in [0:numinst] do
    let curdir := ins[i]!.1
    let dist := ins[i]!.2
    let nextdir := (if i < numinst then ins[i+1]!.1 else ins[0]!.1)
    pos := stepsDir pos curdir dist
    let insideTurn := turningRight curdir nextdir
    out := out + match curdir with
      | .n => if insideTurn then 0 else -pos.1
      | .w => if insideTurn then -(pos.1) * (dist - 1) else -(pos.1) * dist
      | .s => if insideTurn then 0 else pos.1+1
      | .e => if insideTurn then (pos.1 + 1) * (dist - 1) else (pos.1+1) * dist
  return out

-- Walk the path with the "cursor" at the front left
def walkLeft (ins : Array (Direction × Nat)) : Int := Id.run do
  let numinst := ins.size
  let mut pos : Int × Int := ⟨0, 0⟩
  let mut out : Int := 0
  for i in [0:numinst] do
    let curdir := ins[i]!.1
    let dist := ins[i]!.2
    let nextdir := (if i < numinst then ins[i+1]!.1 else ins[0]!.1)
    pos := stepsDir pos curdir dist
    let insideTurn := turningLeft curdir nextdir
    out := out + match curdir with
      | .n => if insideTurn then 0 else pos.1
      | .w => if insideTurn then -(pos.1 + 1) * (dist - 1) else -(pos.1+1) * dist
      | .s => if insideTurn then 0 else -(pos.1+1)
      | .e => if insideTurn then (pos.1) * (dist - 1) else (pos.1) * dist
  return out

def firstPart (input : FilePath) : IO String := do
  let instructions := (← IO.FS.lines input).map (fun s => s.yoloParse parseLine₁)
  let vright := (walkRight instructions).natAbs
  let vleft := (walkLeft instructions).natAbs
  return s!"{max vright vleft}"

--#eval firstPart testinput1           --(ans: 62)
--#eval firstPart testinput2           --(ans: 36)
--#eval firstPart realinput           --(ans: 50603)

/-
PART 2:
-/

def hexToNat (c : Char) : Nat :=
  if ('0' ≤ c ∧ c ≤ '9') then
    c.toNat - 48
  else if ('a' ≤ c ∧ c ≤ 'f') then
    (c.toNat - 97) + 10
  else 0

def hexDigitNat : Parsec Nat := do
  let c ← hexDigit
  return hexToNat c

def parseLine₂ : Parsec (Direction × Nat) := do
  let _ ← anyChar
  ws
  let _ ← natNum
  ws
  let _ ← pstring "(#"
  let num ← exactly 5 hexDigitNat
  let numval := num.foldl (init := 0) fun acc d => acc*16 + d
  let dir ← anyChar
  let _ ← pchar ')'
  match dir with
  | '0' => return ⟨.e, numval⟩
  | '1' => return ⟨.s, numval⟩
  | '2' => return ⟨.w, numval⟩
  | '3' => return ⟨.n, numval⟩
  | _ => fail "Parse error"


def secondPart (input : FilePath) : IO String := do
  let instructions := (← IO.FS.lines input).map (fun s => s.yoloParse parseLine₂)
  let vright := (walkRight instructions).natAbs
  let vleft := (walkLeft instructions).natAbs
  return s!"{max vright vleft}"

--#eval secondPart testinput1           --(ans: 952408144115)
--#eval secondPart realinput           --(ans: 96556251590677)

end Day18
