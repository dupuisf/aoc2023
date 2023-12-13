import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day13

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_13_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_13_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_13"

/-
PART 1:
-/

def parseLine : Parsec (Array Bool) := many1 ((pchar '.' *> pure false) <|> (pchar '#' *> pure true))

def parseGrid : Parsec (Σ n m, Vec₂ n m Bool) := do
  let lines ← sepByA parseLine newlineChar
  let some out := lines.toVec₂ | fail "Rows not all the same size"
  return out

def parseInput : Parsec (Array (Σ (n m : Nat), Vec₂ n m Bool)) :=
  sepByA parseGrid (many1 newlineChar)

def hammingDist [BEq α] (u v : Vec n α) : Nat :=
  let z := u.zipWith v (· != ·)
  z.foldl (init := 0) fun acc x => if x then acc + 1 else acc

def findMirror (grid : Vec₂ n m Bool) (smudging := 0) : Option Nat := do
  if 0 < n then
    for i in [0:n-1] do
      let mut distsofar := 0
      let size := min (i+1) (n-i-1)
      for j in [0:size] do
        let d := hammingDist grid[i-j]! grid[i+1+j]!
        distsofar := distsofar + d
        if distsofar > smudging then break
      if distsofar = smudging then return i
    failure
  else failure

def firstPart (input : FilePath) (smudging := 0) : IO String := do
  let rawdata := (← IO.FS.readFile input)
  let some grids := rawdata.parse? parseInput | return "Parse error"
  let horizMirrors := grids.map fun g => findMirror g.2.2 smudging
  let vertMirrors := grids.map fun g => findMirror g.2.2.transpose smudging
  let horizSum := horizMirrors.foldl (init := 0)
    fun acc m? => match m? with
              | none => acc + 0 | some m => acc + m+1
  let vertSum := vertMirrors.foldl (init := 0)
    fun acc m? => match m? with
              | none => acc + 0 | some m => acc + m+1
  return s!"{vertSum + 100*horizSum}"

--#eval firstPart testinput1           --(ans: 405)
--#eval firstPart testinput2           --(ans: )
--#eval firstPart realinput           --(ans: 30535)

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := firstPart input (smudging := 1)

--#eval secondPart testinput1           --(ans: 400)
--#eval secondPart testinput2           --(ans: )
--#eval secondPart realinput           --(ans: 30844)

end Day13
