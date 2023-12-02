import Aoc2023.Utils

open System

namespace Day03

def testinput : FilePath := "/home/fred/lean/aoc2023/input_03_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_03_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_03"

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

end Day03
