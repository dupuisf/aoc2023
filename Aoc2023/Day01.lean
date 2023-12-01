import Aoc2023.Utils

open System

namespace Day01

def testinput : FilePath := "/home/fred/lean/aoc2023/input_01_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_01_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_01"

/-
PART 1:
-/

def first_part (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  let data := rawdata.map (fun s => s.toCharArray.filter (·.isDigit))
                    |>.map fun as => as[0]!.toNatDigit * 10 + as[as.size-1]!.toNatDigit
  return data.sum

--#eval first_part testinput
--#eval first_part realinput

/-
PART 2:
-/

open Lean Lean.Parsec

def parseNumberForwards : Parsec Nat :=
  natDigit
  <|> (do let _ ← pstring "zero"; return 0)
  <|> (do let _ ← pstring "one"; return 1)
  <|> (do let _ ← pstring "two"; return 2)
  <|> (do let _ ← pstring "three"; return 3)
  <|> (do let _ ← pstring "four"; return 4)
  <|> (do let _ ← pstring "five"; return 5)
  <|> (do let _ ← pstring "six"; return 6)
  <|> (do let _ ← pstring "seven"; return 7)
  <|> (do let _ ← pstring "eight"; return 8)
  <|> (do let _ ← pstring "nine"; return 9)

def parseNumberBackwards : Parsec Nat :=
  natDigit
  <|> (do let _ ← pstring "zero".reverse; return 0)
  <|> (do let _ ← pstring "one".reverse; return 1)
  <|> (do let _ ← pstring "two".reverse; return 2)
  <|> (do let _ ← pstring "three".reverse; return 3)
  <|> (do let _ ← pstring "four".reverse; return 4)
  <|> (do let _ ← pstring "five".reverse; return 5)
  <|> (do let _ ← pstring "six".reverse; return 6)
  <|> (do let _ ← pstring "seven".reverse; return 7)
  <|> (do let _ ← pstring "eight".reverse; return 8)
  <|> (do let _ ← pstring "nine".reverse; return 9)

partial def getFirstNum : Parsec Nat :=
  parseNumberForwards <|> (do let _ ← anyChar; getFirstNum)

partial def getFirstNumBackwards : Parsec Nat :=
  parseNumberBackwards <|> (do let _ ← anyChar; getFirstNumBackwards)

def second_part (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  let firstDigits := rawdata.map fun s => s.yoloParse getFirstNum
  let lastDigits := rawdata.map fun s => s.reverse.yoloParse getFirstNumBackwards
  let lines := firstDigits.zipWith lastDigits fun a b => 10*a + b
  return lines.sum

--#eval second_part testinput2
--#eval second_part realinput

end Day01
