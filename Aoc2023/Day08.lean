import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day08

def testinput : FilePath := "/home/fred/lean/aoc2023/input_08_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_08_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_08"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval firstPart testinput           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval secondPart testinput           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day08
