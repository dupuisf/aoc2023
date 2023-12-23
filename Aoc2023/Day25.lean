import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day25

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_25_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_25_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_25"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

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

end Day25
