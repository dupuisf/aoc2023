import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day04

def testinput : FilePath := "/home/fred/lean/aoc2023/input_04_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_04_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_04"

/-
PART 1:
-/


def parseCard : Parsec ((List Nat) × (List Nat)) := do
  let _ ← pstring "Card"
  ws
  let _ ← natNum
  let _ ← pchar ':'
  ws
  let lst1 ← sepBy natNum whites
  ws
  let _ ← pchar '|'
  ws
  let lst2 ← sepBy natNum whites
  return ⟨lst1, lst2⟩

def score (n : Nat) := if n = 0 then 0 else 2^(n-1)

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  let parsed := rawdata.map fun s => s.yoloParse parseCard
  let intersections := parsed.map fun card => card.1.filter (card.2.contains ·)
  let scores := intersections.map fun lst => score lst.length
  return scores.sum

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

end Day04
