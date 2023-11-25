import Aoc2023.Utils

open System

namespace DayXX

def testinput : FilePath := "/home/fred/lean/aoc2023/input_XX_test"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_XX"

/-
PART 1:
-/

def first_part (input : FilePath) : IO Nat := do
  IO.println ""
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval first_part testinput
--#eval first_part realinput

/-
PART 2:
-/

def second_part (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval second_part testinput
--#eval second_part realinput

end DayXX
