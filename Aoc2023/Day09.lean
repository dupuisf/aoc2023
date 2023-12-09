import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day09

def testinput : FilePath := "/home/fred/lean/aoc2023/input_09_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_09_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_09"

/-
PART 1:
-/

def toDiffs : List Int → Int × List Int
| [] => panic! "Not enough elements"
| fst :: [] => ⟨fst, []⟩
| fst :: rest =>
  let ⟨snd, rest'⟩ := toDiffs rest
  ⟨fst, (snd - fst) :: rest'⟩

partial def toDiffSeq (as : List Int) : List Int :=
  match as with
  | [] => []
  | head :: tail =>
    let ⟨fst, diffs⟩ := toDiffs (head :: tail)
    fst :: (toDiffSeq diffs)

def ofDiffs (fst : Int) (diffs : List Int) : List Int :=
  match diffs with
  | [] => [fst]
  | head :: tail =>
    let out := ofDiffs (fst + head) tail
    fst :: out

def ofDiffSeq : List Int → List Int
| [] => []
| fst :: rest =>
  let diffs := ofDiffSeq rest
  ofDiffs fst diffs

def extrapolate (as : List Int) : Int := Id.run do
  let some x := (ofDiffSeq ((toDiffSeq as) ++ [0])).getLast? | panic! "Oh no"
  return x

def firstPart (input : FilePath) : IO Int := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let numbers := rawdata.map fun s => s.map String.toInt!
  let extravalues := (numbers.map toDiffSeq).map ofDiffSeq |>.map extrapolate
  return extravalues.sum

--#eval firstPart testinput           --(ans: 114)
--#eval firstPart realinput           --(ans: 2005352194)

/-
PART 2:
-/

def secondPart (input : FilePath) : IO Int := do
  let rawdata := (← IO.FS.lines input).map String.splitOn
  let numbers := rawdata.map (fun s => s.map String.toInt!) |>.map List.reverse
  let extravalues := (numbers.map toDiffSeq).map ofDiffSeq |>.map extrapolate
  return extravalues.sum

--#eval secondPart testinput           --(ans: 2)
--#eval secondPart realinput           --(ans: 1077)

end Day09
