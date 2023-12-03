import Aoc2023.Utils

open System

namespace Day01

def testinput : FilePath := "/home/fred/lean/aoc2023/input_01_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_01_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_01"

/-
PART 1:
-/

def firstPart (input : FilePath) : IO Nat := do
  let rawdata ← IO.FS.lines input
  let data := rawdata.map (fun s => s.toCharArray.filter (·.isDigit))
                    |>.map fun as => as[0]!.toNatDigit * 10 + as[as.size-1]!.toNatDigit
  return data.sum

--#eval firstPart testinput   -- Correct answer: 142
--#eval firstPart realinput   -- Correct answer: 54927

/-
PART 2:
-/

open Lean Lean.Parsec

def parseNumberForwards : Parsec Nat :=
  natDigit
  <|> (pstring "zero" *> return 0)
  <|> (pstring "one" *> return 1)
  <|> (pstring "two" *> return 2)
  <|> (pstring "three" *> return 3)
  <|> (pstring "four" *> return 4)
  <|> (pstring "five" *> return 5)
  <|> (pstring "six" *> return 6)
  <|> (pstring "seven" *> return 7)
  <|> (pstring "eight" *> return 8)
  <|> (pstring "nine" *> return 9)

def parseNumberBackwards : Parsec Nat :=
  natDigit
  <|> (pstring "zero".reverse *> return 0)
  <|> (pstring "one".reverse *> return 1)
  <|> (pstring "two".reverse *> return 2)
  <|> (pstring "three".reverse *> return 3)
  <|> (pstring "four".reverse *> return 4)
  <|> (pstring "five".reverse *> return 5)
  <|> (pstring "six".reverse *> return 6)
  <|> (pstring "seven".reverse *> return 7)
  <|> (pstring "eight".reverse *> return 8)
  <|> (pstring "nine".reverse *> return 9)

def getFirstNum : Parsec Nat := fix fun p => parseNumberForwards <|> (anyChar *> p)

def getFirstNumBackwards : Parsec Nat := fix fun p => parseNumberBackwards <|> (anyChar *> p)

def secondPart (input : FilePath) : IO Nat := do
  let rawdata ← IO.FS.lines input
  let firstDigits := rawdata.map fun s => s.yoloParse getFirstNum
  let lastDigits := rawdata.map fun s => s.reverse.yoloParse getFirstNumBackwards
  return firstDigits.zipWith lastDigits (10*· + ·) |>.sum

--#eval secondPart testinput2   -- Correct answer: 281
--#eval secondPart realinput    -- Correct answer: 54581

end Day01
