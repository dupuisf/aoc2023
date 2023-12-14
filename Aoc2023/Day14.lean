import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day14

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_14_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_14_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_14"

/-
PART 1:
-/

def printGrid (grid : Vec₂ n m Char) : IO Unit := do
  for hi : i in [0:n] do
    IO.println <| String.ofCharArray grid[i].val

def parseLine : Parsec (Array Char) :=
  many1 ((pchar '.') <|> (pchar '#') <|> (pchar 'O'))

def parseGrid : Parsec (Σ n m, Vec₂ n m Char) := do
  let lines ← sepByA parseLine newlineChar
  let some out := lines.toVec₂ | fail "Rows not all the same size"
  return out

def calcLoad (grid : Vec₂ n m Char) : Nat := Id.run do
  let mut sum := 0
  for hi : i in [0:n] do
    let rowload := n - i
    let cursum := grid[i].foldl (init := 0) fun acc c => acc + rowload * if c == 'O' then 1 else 0
    sum := sum + cursum
  return sum

def tiltBlockNorth (grid : Vec₂ n m Char) (i j : Nat) : Nat :=
  if hi : 0 < i then
    if grid[i-1]![j]! == '.' then
      tiltBlockNorth grid (i-1) j
    else i
  else 0

def tiltPlaneNorth (grid : Vec₂ n m Char) : Vec₂ n m Char := Id.run do
  let mut curGrid := grid
  for hi : i in [0:n] do
    for hj : j in [0:m] do
      if curGrid[i][j] == 'O' then
        let new_i := tiltBlockNorth curGrid i j
        curGrid := (curGrid.set! i j '.').set! new_i j 'O'
  return curGrid

def firstPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.readFile input).parse? parseGrid | return "Parse error"
  let tiltedGrid := tiltPlaneNorth grid
  return s!"{calcLoad tiltedGrid}"

def debug1 (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.readFile input).parse? parseGrid | return "Parse error"
  --let grid := rawdata.2.2
  let tiltedGrid := tiltPlaneNorth grid
  printGrid tiltedGrid
  return "ok"

--#eval firstPart testinput1           --(ans: 136)
--#eval debug1 testinput1           --(ans: 136)
--#eval firstPart testinput2           --(ans: 136)
--#eval firstPart realinput           --(ans: 106990)

/-
PART 2: Figured out the pattern by hand while debugging and couldn't be bother to actually
code it properly.
-/

partial def tiltBlockSouth (grid : Vec₂ n m Char) (i j : Nat) : Nat :=
  if hi : i < n-1 then
    if grid[i+1]![j]! == '.' then
      tiltBlockSouth grid (i+1) j
    else i
  else n-1

def tiltPlaneSouth (grid : Vec₂ n m Char) : Vec₂ n m Char := Id.run do
  let mut curGrid := grid
  for hi : i in [1:n+1] do
    for hj : j in [0:m] do
      if curGrid[n-i]![j] == 'O' then
        let new_i := tiltBlockSouth curGrid (n-i) j
        curGrid := (curGrid.set! (n-i) j '.').set! new_i j 'O'
  return curGrid

partial def tiltBlockEast (grid : Vec₂ n m Char) (i j : Nat) : Nat :=
  if hj : j < m-1 then
    if grid[i]![j+1]! == '.' then
      tiltBlockEast grid i (j+1)
    else j
  else m-1

def tiltPlaneEast (grid : Vec₂ n m Char) : Vec₂ n m Char := Id.run do
  let mut curGrid := grid
  for hj : j in [1:m+1] do
    for hi : i in [0:n] do
      if curGrid[i][m-j]! == 'O' then
        let new_j := tiltBlockEast curGrid i (m-j)
        curGrid := (curGrid.set! i (m-j) '.').set! i new_j 'O'
  return curGrid

partial def tiltBlockWest (grid : Vec₂ n m Char) (i j : Nat) : Nat :=
  if hj : 0 < j then
    if grid[i]![j-1]! == '.' then
      tiltBlockWest grid i (j-1)
    else j
  else 0

def tiltPlaneWest (grid : Vec₂ n m Char) : Vec₂ n m Char := Id.run do
  let mut curGrid := grid
  for hj : j in [0:m] do
    for hi : i in [0:n] do
      if curGrid[i][j] == 'O' then
        let new_j := tiltBlockWest curGrid i j
        curGrid := (curGrid.set! i j '.').set! i new_j 'O'
  return curGrid

def cycle (grid : Vec₂ n m Char) : Vec₂ n m Char := Id.run do
  let north := tiltPlaneNorth grid
  let west := tiltPlaneWest north
  let south := tiltPlaneSouth west
  let east := tiltPlaneEast south
  return east

def debug3 (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.readFile input).parse? parseGrid | return "Parse error"
  let north := tiltPlaneNorth grid
  let west := tiltPlaneWest north
  let south := tiltPlaneSouth west
  let east := tiltPlaneEast south
  printGrid grid
  IO.println "----"
  printGrid north
  IO.println "----"
  printGrid west
  IO.println "----"
  printGrid south
  IO.println "----"
  printGrid east
  return "ok"

def debug2 (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.readFile input).parse? parseGrid | return "Parse error"
  let cycle1 := cycle grid
  let cycle2 := cycle cycle1
  let cycle3 := cycle cycle2
  printGrid grid
  IO.println "----"
  printGrid cycle1
  IO.println "----"
  printGrid cycle2
  IO.println "----"
  printGrid cycle3
  return "ok"

def manyCycles (curGrid : Vec₂ n m Char) (remaining := 3) : Vec₂ n m Char :=
  if remaining = 0 then curGrid
  else
    let newGrid := cycle curGrid
    if newGrid == curGrid then
      --let newscore := calcLoad newGrid
      newGrid
    else
      manyCycles newGrid (remaining-1)

def manyCyclesDebug (curGrid : Vec₂ n m Char) (remaining thresh : Nat) : IO (Vec₂ n m Char) := do
  if remaining < thresh then IO.println s!"remaining {remaining}, load = {calcLoad curGrid}"
  if remaining = 0 then return curGrid
  else
    let newGrid := cycle curGrid
    if newGrid == curGrid then
      --let newscore := calcLoad newGrid
      return newGrid
    else
      return ← manyCyclesDebug newGrid (remaining-1) thresh

def secondPart (input : FilePath) (numIter : String) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.readFile input).parse? parseGrid | return "Parse error"
  let numCycles := numIter.toNat!
  let cycledGrid ← manyCyclesDebug grid numCycles 100
  --printGrid cycledGrid
  return s!"{calcLoad cycledGrid}"

--#eval secondPart testinput1           --(ans: )
--#eval debug2 testinput1           --(ans: )
--#eval debug3 testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

-- #eval (1000000000 - 935) % 39 -- 33   => 100531 is the answer...

end Day14
