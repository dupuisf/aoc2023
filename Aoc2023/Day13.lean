import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day13

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_13_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_13_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_13"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return "bla"

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return "bla"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day13
