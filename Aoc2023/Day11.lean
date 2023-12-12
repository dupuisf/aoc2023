import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day11

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_11_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_11_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_11"

/-
PART 1:
-/

def printGrid (grid : Array₂ Char) : IO Unit := do
  for row in grid do
    IO.println <| row.foldl (init := "") fun acc c => acc.push c

def expandRows (grid : Array₂ Char) : Array₂ Char :=
  grid.concatMap fun row => if row.all (· == '.') then #[row, row] else #[row]

def dist (a b : Nat × Nat) : Nat :=
  let x₁ : Int := a.1
  let x₂ : Int := b.1
  let y₁ : Int := a.2
  let y₂ : Int := b.2
  Int.natAbs (x₂ - x₁) + Int.natAbs (y₂ - y₁)

def firstPart (input : FilePath) : IO String := do
  let some tmpGrid := (← IO.FS.lines input).map String.toCharArray
                    |> expandRows |>.transpose |>.map expandRows | return "Error"
  let some expanded := tmpGrid.transpose | return "Error"
  let galaxies := expanded.findAllIdx₂ (· == '#')
  let mut out := 0
  for i in [1:galaxies.size] do
    for j in [0:i] do
      out := out + dist galaxies[i]! galaxies[j]!
  return s!"{out}"

--#eval firstPart testinput1           --(ans: 374)
--#eval firstPart realinput           --(ans: 9623138)

/-
PART 2:
-/

def countBetween (xs : Array Nat) (a b : Nat) : Nat :=
  xs.foldl (init := 0) fun acc val => if a ≤ val ∧ val ≤ b then acc+1 else acc

def dist₂ (emptyRows emptyCols : Array Nat) (a b : Nat × Nat) (factor := 1000000) : Nat :=
  let x₁ := min a.1 b.1
  let x₂ := max a.1 b.1
  let y₁ := min a.2 b.2
  let y₂ := max a.2 b.2
  let numbigrows := countBetween emptyRows x₁ x₂
  let numbigcols := countBetween emptyCols y₁ y₂
  x₂ - x₁ + (factor-1) * numbigrows + y₂ - y₁ + (factor-1) * numbigcols

def secondPart (input : FilePath) : IO String := do
  let grid := (← IO.FS.lines input).map String.toCharArray
  let some gridT := grid.transpose | return "Rows not all the same length"
  let emptyRows := grid.findAllIdx (fun row => row.all (· == '.'))
  let emptyCols := gridT.findAllIdx (fun row => row.all (· == '.'))
  let galaxies := grid.findAllIdx₂ (· == '#')
  let mut out := 0
  for hi : i in [1:galaxies.size] do
    for hj : j in [0:i] do
      have hj : j < galaxies.size := Nat.lt_trans (hj.2) hi.2
      out := out + dist₂ emptyRows emptyCols galaxies[i] galaxies[j]
  return s!"{out}"

--#eval secondPart testinput1           --(ans: 1030 with factor 10, 8410 with factor 100)
--#eval secondPart realinput           --(ans: 726820169514)

end Day11
