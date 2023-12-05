import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day04

def testinput : FilePath := "/home/fred/lean/aoc2023/input_04_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_04_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_04"

/-
PART 1:
-/


def parseCard : Parsec (Nat × List Nat × List Nat) := do
  let _ ← pstring "Card"
  ws
  let n ← natNum
  let _ ← pchar ':'
  ws
  let lst1 ← sepBy natNum whites
  ws
  let _ ← pchar '|'
  ws
  let lst2 ← sepBy natNum whites
  return ⟨n, lst1, lst2⟩

def score (n : Nat) := if n = 0 then 0 else 2^(n-1)

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  let parsed := rawdata.map fun s => s.yoloParse parseCard
  let intersections := parsed.map fun card => card.2.1.filter (card.2.2.contains ·)
  let scores := intersections.map fun lst => score lst.length
  return scores.sum

--#eval firstPart testinput    --(ans: 13)
--#eval firstPart realinput    --(ans: 28538)

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input)
  let parsed := rawdata.map fun s => s.yoloParse parseCard
  let intersections := parsed.map fun card => card.2.1.filter (card.2.2.contains ·)
  let numInter := intersections.map (·.length)
  let mut dups := mkArray numInter.size 1
  for hi : i in [0:numInter.size] do
    for hj₁ : j in [i+1:i+1+numInter[i]'hi.2] do
      if hj : j < dups.size then
        have : i < dups.size := by
          calc i ≤ i + 1 := Nat.le_succ _
               _ ≤ j := hj₁.1
               _ < dups.size := hj
        dups := dups.set ⟨j, hj⟩ (dups[j] + dups[i])
  return dups.sum

--#eval secondPart testinput   --(ans: 30)
--#eval secondPart realinput   --(ans: 9425061)

end Day04
