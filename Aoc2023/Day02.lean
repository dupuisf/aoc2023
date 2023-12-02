import Aoc2023.Utils

open System Lean Lean.Parsec

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

structure Triple where
  r : Nat
  g : Nat
  b : Nat

instance : ToString Triple where
  toString t := s!"⟪{t.r}, {t.g}, {t.b}⟫"

def parseColor : Parsec Color :=
  (do let _ ← pstring "red"; return .red)
  <|> (do let _ ← pstring "green"; return .green)
  <|> (do let _ ← pstring "blue"; return .blue)

def parseItem : Parsec (Nat × Color) := do
  let num ← natNum
  ws
  let color ← parseColor
  return ⟨num, color⟩

def parseRound : Parsec Triple := do
  let items ← (sepBy parseItem (pstring ", "))
  return items.foldl (init := (⟨0,0,0⟩ : Triple)) fun cur item =>
    match item.2 with
    | .red => ⟨item.1, cur.g, cur.b⟩
    | .green => ⟨cur.r, item.1, cur.b⟩
    | .blue => ⟨cur.r, cur.g, item.1⟩

def parseGame : Parsec (List Triple) :=
  (pstring "Game ") >> natNum >> pstring ": " >> sepBy parseRound (pstring "; ")

def roundPossible (round : Triple) : Bool :=
  round.r ≤ 12 ∧ round.g ≤ 13 ∧ round.b ≤ 14

def gamePossible (game : List Triple) := Id.run do
  for round in game do
    if ¬(roundPossible round) then return false
  return true

def firstPart (input : FilePath) : IO Nat := do
  let rawdata ← IO.FS.lines input
  let games := rawdata.map fun s => s.yoloParse parseGame
  let possibles := games.map gamePossible
  return possibles.data.foldlIdx (init := 0) fun idx sum cur => if cur then sum+idx+1 else sum

--#eval firstPart testinput    --(ans : 8)
--#eval firstPart realinput  --(ans: 2776)

/-
PART 2:
-/

instance : Max Triple where
  max x y := ⟨max x.r y.r, max x.g y.g, max x.b y.b⟩

def smallest (g : List Triple) : Triple :=
  g.foldl (init := ⟨0,0,0⟩) max

def secondPart (input : FilePath) : IO Nat := do
  let rawdata ← IO.FS.lines input
  let games := rawdata.map fun s => s.yoloParse parseGame
  let smallests := games.map smallest
  return smallests.foldl (init := 0) fun sum t => sum + t.r * t.g * t.b

--#eval secondPart testinput  -- (ans: 2286)
--#eval secondPart realinput   -- (ans: 68638)

end Day02
