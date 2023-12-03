import Aoc2023.Utils

open System

namespace Day03

def testinput : FilePath := "/home/fred/lean/aoc2023/input_03_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_03_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_03"

/-
PART 1:
-/

structure Number where
  val : Nat
  row : Nat
  start : Nat
  stop : Nat

instance : ToString Number where
  toString n := s!"⟪{n.val}, {n.row}, ({n.start}, {n.stop})⟫"

def printGrid (grid : Array₂ Char) : IO Unit := do
  for line in grid do
    IO.println (String.ofCharArray line)

def _root_.Char.isSymbol (c : Char) : Bool :=
  if c == '.' then false
  else if c.isDigit then false else true

def checkIfNextToSymbol (g : Array₂ Char) (n : Number) : Bool := Id.run do
  -- row above
  for j in [n.start-1:n.stop+2] do
    if g[n.row-1]![j]!.isSymbol then return true
  -- Row below
  for j in [n.start-1:n.stop+2] do
    if g[n.row+1]![j]!.isSymbol then return true
  -- Left
  if g[n.row]![n.start-1]!.isSymbol then return true
  -- Right
  if g[n.row]![n.stop+1]!.isSymbol then return true
  return false

def getNumbers (grid : Array₂ Char) : Array Number := Id.run do
  let w := grid[0]!.size
  let h:= grid.size
  let mut nums : Array Number := #[]
  for i in [1:h] do
    let mut prevIsDigit := false
    let mut numStart := 0
    let mut num := 0
    for j in [1:w] do
      if grid[i]![j]!.isDigit ∧ ¬prevIsDigit then
        numStart := j
        prevIsDigit := true
      else if ¬grid[i]![j]!.isDigit ∧ prevIsDigit then
        nums := nums.push ⟨num, i, numStart, j-1⟩
        num := 0
        prevIsDigit := false
      if grid[i]![j]!.isDigit then
        num := num * 10 + grid[i]![j]!.toNatDigit
  return nums

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let origwidth := rawdata[0]!.size
  let padded1 := #[Array.mkArray origwidth '.'] ++ rawdata ++ #[Array.mkArray origwidth '.']
  let grid := padded1.map fun as => #['.'] ++ as ++ #['.']
  let nums := getNumbers grid

  return nums.foldl (init := 0)
    fun sum n => if checkIfNextToSymbol grid n then sum + n.val else sum

--#eval firstPart testinput    --(ans: 4361)
--#eval firstPart realinput    --(ans: 549908)

/-
PART 2:
-/

def findGearsNextDoor (g : Array₂ Char) (n : Number) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  -- row above
  for j in [n.start-1:n.stop+2] do
    if g[n.row-1]![j]! == '*' then out := out.push ⟨n.row-1, j⟩
  -- Row below
  for j in [n.start-1:n.stop+2] do
    if g[n.row+1]![j]! == '*' then out := out.push ⟨n.row+1, j⟩
  -- Left
  if g[n.row]![n.start-1]! == '*' then out := out.push ⟨n.row, n.start-1⟩
  -- Right
  if g[n.row]![n.stop+1]! == '*' then out := out.push ⟨n.row, n.stop+1⟩
  return out

def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let origwidth := rawdata[0]!.size
  let padded1 := #[mkArray origwidth '.'] ++ rawdata ++ #[mkArray origwidth '.']
  let grid := padded1.map fun as => #['.'] ++ as ++ #['.']
  let nums := getNumbers grid

  let w := origwidth + 2
  let h := grid.size
  -- For every position, array of adjacent numbers if it's a gear
  -- Horribly inefficient but whatever
  let mut gears : Array₂ (Array Nat) := .mkArray₂ h w #[]
  for n in nums do
    let gs := findGearsNextDoor grid n
    for pos in gs do
      gears := gears.set₂ pos.1 pos.2 (gears[pos.1]![pos.2]!.push n.val)

  let mut output := 0
  for i in [1:h] do
    for j in [1:w] do
      if gears[i]![j]!.size = 2 then output := output + (gears[i]![j]!.foldl (init := 1) (· * ·))
  return output

--#eval secondPart testinput   --(ans: 467835)
--#eval secondPart realinput   --(ans: 81166799)

end Day03
