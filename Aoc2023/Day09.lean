import Aoc2023.Utils

open System

namespace Day09

def testinput : FilePath := "/home/fred/lean/aoc2023/input_09_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_09_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_09"

/-
PART 1:
-/

def toDiffs (as : List Int) (h : as ≠ []) : Int × List Int :=
  match as with
  | [] => False.elim (h rfl)
  | fst :: [] => ⟨fst, []⟩
  | head :: neck :: tail =>
    let ⟨snd, rest'⟩ := toDiffs (neck :: tail) (by simp)
    ⟨head, (snd - head) :: rest'⟩

theorem toDiffs_length_lt (as : List Int) (h : as ≠ []) : (toDiffs as h).2.length < as.length := by
  match as with
  | [] => exact False.elim (h rfl)
  | _ :: [] => simp [toDiffs]
  | head :: neck :: tail =>
    simp only [toDiffs]
    refine Nat.succ_lt_succ ?_
    calc _ < (neck :: tail).length := toDiffs_length_lt _ (by simp)
         _ = tail.length + 1 := by simp

def toDiffSeq : List Int → List Int
| [] => []
| head :: tail =>
  let out := toDiffs (head :: tail) (by simp)
  have : out.2.length < tail.length + 1 := toDiffs_length_lt _ _
  out.1 :: (toDiffSeq out.2)
termination_by toDiffSeq as => as.length

def ofDiffs (fst : Int) : List Int → List Int
| [] => [fst]
| head :: tail => fst :: (ofDiffs (fst + head) tail)

def ofDiffSeq : List Int → List Int
| [] => []
| fst :: rest => ofDiffs fst (ofDiffSeq rest)

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
