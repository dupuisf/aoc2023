import Aoc2023.Utils

open System

namespace Day02

def testinput : FilePath := "/home/fred/lean/aoc2023/input_02_test"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_02"

/-
PART 1:
-/

inductive Color
| red
| green
| blue
deriving BEq, Repr

instance : ToString Color where
  toString c := match c with
                | .red => "red"
                | .green => "green"
                | .blue => "blue"


def _root_.String.toColor : String → Color
| "red" => .red
| "green" => .green
| "blue" => .blue
| _ => .red

/-- "2 blue" -> ⟨2, .blue⟩ -/
def getItem (s : String) : Nat × Color :=
  let l := s.splitOn " "
  ⟨l[0]!.toNat!, l[1]!.toColor⟩

def getRound (s : String) : Nat × Nat × Nat :=
  let spl := (s.split (· == ',')).map String.trim
  let items := spl.map getItem
  items.foldl (init := ⟨0,0,0⟩) fun cur item =>
    match item.2 with
    | .red => ⟨item.1, cur.2.1, cur.2.2⟩
    | .green => ⟨cur.1, item.1, cur.2.2⟩
    | .blue => ⟨cur.1, cur.2.1, item.1⟩

def getGame (s : String) : List (Nat × Nat × Nat) :=
  (s.split (· == ';') |>.map String.trim).map getRound

def roundPossible (g : Nat × Nat × Nat) : Bool :=
  g.1 ≤ 12 ∧ g.2.1 ≤ 13 ∧ g.2.2 ≤ 14

def gamePossible (g : List (Nat × Nat × Nat)) := Id.run do
  for r in g do
    if ¬(roundPossible r) then return false
  return true

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map fun s => (s.dropWhile (· != ':')).drop 2
  let games := rawdata.map getGame
  let possibles := games.map gamePossible
  return possibles.data.foldlIdx (init := 0) fun idx sum cur => if cur then sum+idx+1 else sum

--#eval firstPart testinput
--#eval firstPart realinput  (Ans: 2776)

/-
PART 2:
-/

def smallestPossibleRed (g : List (Nat × Nat × Nat)) : Nat :=
  g.foldl (init := 0) fun min cur => if min < cur.1 then cur.1 else min

def smallestPossibleGreen (g : List (Nat × Nat × Nat)) : Nat :=
  g.foldl (init := 0) fun min cur => if min < cur.2.1 then cur.2.1 else min

def smallestPossibleBlue (g : List (Nat × Nat × Nat)) : Nat :=
  g.foldl (init := 0) fun min cur => if min < cur.2.2 then cur.2.2 else min

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map fun s => (s.dropWhile (· != ':')).drop 2
  let games := rawdata.map getGame
  let minRed := games.map smallestPossibleRed
  let minGreen := games.map smallestPossibleGreen
  let minBlue := games.map smallestPossibleBlue
  let rg := minRed.zipWith minGreen (· * ·)
  return (rg.zipWith minBlue (· * ·)).sum

--#eval secondPart testinput
--#eval secondPart realinput

end Day02
