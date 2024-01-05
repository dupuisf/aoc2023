import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day24

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_24_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_24_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_24"

/-
PART 1:
-/

structure Hailstone where
  x : Rat
  y : Rat
  z : Rat
  dx : Rat
  dy : Rat
  dz : Rat
deriving Repr, BEq, Inhabited, DecidableEq

instance : ToString Hailstone where
  toString s := s!"({s.x}, {s.y}, {s.z}) @ ({s.dx}, {s.dy}, {s.dz})"

inductive EQ
| infty
| neginfty
| rat (r : Rat)
deriving Repr, BEq, Inhabited, DecidableEq

notation "∞" => EQ.infty
notation "-∞" => EQ.neginfty

def Hailstone.slope (s : Hailstone) : EQ :=
  if s.dx = 0 then (if s.dy > 0 then ∞ else -∞) else .rat <| (s.dy : Rat) / s.dx

def Hailstone.const (s : Hailstone) : Option Rat :=
  match s.slope with
  | ∞ => none
  | -∞ => none
  | .rat a => s.y - a * s.x

def Hailstone.intersection (s₁ s₂ : Hailstone) (x₁ y₁ x₂ y₂ : Rat) : Bool :=
  match s₁.slope, s₂.slope with
  | ∞, ∞ =>
      let cond1 : Bool := s₁.x = s₂.x
      let cond2 : Bool := x₁ ≤ s₁.x ∧ s₁.x ≤ x₂
      let cond3 : Bool := s₁.y ≤ y₂
      let cond3 : Bool := s₂.y ≤ y₂
      if cond1 ∧ cond2 ∧ cond3 then true else false
  | ∞, -∞ => sorry
  | -∞, ∞ => sorry
  | -∞, -∞ => sorry
  | ∞, .rat a₂ => sorry
  | -∞, .rat a₂ => sorry
  | .rat a₁, ∞ => sorry
  | .rat a₁, -∞ => sorry
  | .rat a₁, .rat a₂ =>
      if a₁ = a₂ then
        sorry
      else
        let x := ((s₂.y - a₁ * s₁.x) - (s₂.y - a₂ * s₂.x))
        let y := a₁ * x + (s₂.y - a₁ * s₁.x)
        let cond1 : Bool := (x - s₁.x) * s₁.dx ≥ 0
        let cond2 : Bool := (x - s₂.x) * s₂.dx ≥ 0
        let cond3 : Bool := (y - s₁.y) * s₁.dy ≥ 0
        let cond4 : Bool := (y - s₂.y) * s₂.dy ≥ 0
        let cond5 : Bool := x₁ ≤ x ∧ x ≤ x₂
        let cond6 : Bool := y₁ ≤ y ∧ y ≤ y₂
        if cond1 ∧ cond2 ∧ cond3 ∧ cond4 then true else false

def parseHailstone : Parsec Hailstone := do
  let x ← intNum
  skipString ","; ws
  let y ← intNum
  skipString ","; ws
  let z ← intNum
  ws; skipString "@"; ws
  let dx ← intNum
  skipString ","; ws
  let dy ← intNum
  skipString ","; ws
  let dz ← intNum
  return ⟨x,y,z,dx,dy,dz⟩  -- FIXME

def firstPart (input : FilePath) : IO String := do
  let some stones := (← IO.FS.lines input).mapM fun s => s.parse? parseHailstone
    | return "Parse error"
  return s!"{stones}"

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day24
