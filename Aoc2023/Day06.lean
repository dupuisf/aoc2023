import Aoc2023.Utils

open System

namespace Day06

def testinput : FilePath := "/home/fred/lean/aoc2023/input_06_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_06_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_06"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval firstPart testinput
--#eval firstPart realinput

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval secondPart testinput
--#eval secondPart realinput

end Day06
