import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day10

def testinput : FilePath := "/home/fred/lean/aoc2023/input_10_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_10_test2"
def testinput3 : FilePath := "/home/fred/lean/aoc2023/input_10_test3"
def testinput4 : FilePath := "/home/fred/lean/aoc2023/input_10_test4"
def testinput5 : FilePath := "/home/fred/lean/aoc2023/input_10_test5"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_10"

-- FOR UTILS

/-
PART 1:
-/

inductive Direction
| n | w | e | s
deriving BEq, Repr

instance : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"


instance : HAdd (Nat × Nat) Direction (Nat × Nat) where
  hAdd x y := match y with
              | .n => ⟨x.1-1, x.2⟩ | .w => ⟨x.1, x.2 - 1⟩ | .e => ⟨x.1, x.2 + 1⟩ | .s => ⟨x.1+1, x.2⟩

def Direction.foldM {m : Type _ → Type _} [Monad m] (init : α) (f : α → Direction → m α) : m α := do
  let n ← f init .n
  let w ← f n .w
  let e ← f w .e
  let s ← f e .s
  return s

def Direction.fold (init : α) (f : α → Direction → α) : α :=
  Id.run <| Direction.foldM init f

def Direction.flip : Direction → Direction
| .n => .s | .w => .e | .e => .w | .s => .n

def canGoTo : Char → List Direction
| '|' => [.n, .s] | '-' => [.e, .w] | 'L' => [.n, .e]
| 'J' => [.n, .w] | '7' => [.s, .w]
| 'F' => [.s, .e] | 'S' => [.n, .s, .e, .w]
| _ => []

def next (dir : Direction) (c : Char) : Option Direction :=
  let lst : List Direction := match c with
  | '|' => [.n, .s] | '-' => [.e, .w] | 'L' => [.n, .e]
  | 'J' => [.n, .w] | '7' => [.s, .w]
  | 'F' => [.s, .e] | 'S' => [.n, .s, .e, .w] | _ => []
  match lst.filter (fun x => x != dir.flip) with
  | [elem] => some elem
  | _ => none

def possibleSteps (grid : Array₂ Char) (pos : Nat × Nat) (doubleStep := false) : List Direction :=
  (canGoTo grid[pos.1]![pos.2]!).foldl (init := []) fun acc dir =>
    let newpos := if doubleStep then pos + dir + dir else pos + dir
    let possibleDirs := canGoTo grid[newpos.1]![newpos.2]!
    if possibleDirs.contains dir.flip then
      dir :: acc
    else acc

partial def walk (grid : Array₂ Char) (pos : Nat × Nat) (fromDir : Direction) (clock := 0)
    (doubleStep := false) : Nat := Id.run do
  let some dir := next fromDir grid[pos.1]![pos.2]! | panic! "Can't keep going"
  let newpos := if doubleStep then pos + dir + dir else pos + dir
  if (grid[newpos.1]![newpos.2]! == 'S') then return (clock + 1)
  else return walk grid newpos dir (clock + 1)

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨h_nonempty⟩ := checkThat rawdata fun as => 0 < as.size | return "Error: no input"
  let origwidth := rawdata[0].size
  let padded1 := #[Array.mkArray origwidth '.'] ++ rawdata ++ #[Array.mkArray origwidth '.']
  let grid := padded1.map fun as => #['.'] ++ as ++ #['.']
  --let n := grid.size
  --let some ⟨hn⟩ := checkThat n fun z => 0 < z | panic! "n = 0"
  --let m := grid[0].size
  --let some ⟨hm⟩ := checkThat m fun z => 0 < z | panic! "m = 0"
  --let some ⟨hgrid⟩ :=
  --  grid.checkThatAll fun as => as.size = m | panic! "Rows not all the same size!"

  let some startPos := grid.findIdx₂ (fun x => x == 'S') | return "Can't find starting point"
  let startDir :: _ := possibleSteps grid startPos | return "No possible starting direction"
  return s!"{(1 + (walk grid (startPos + startDir) startDir)) / 2}"

--#eval firstPart testinput           --(ans: 4)
--#eval firstPart testinput2           --(ans: 8)
--#eval firstPart realinput           --(ans: 6831)

/-
PART 2:
-/

def puffRow (row : Array Char) : Array Char :=
  #['*'] ++ ((#['·'] ++ row.concatMap fun c => #[c, '·']).push '*')

def puffGrid (grid : Array₂ Char) : Array₂ Char := Id.run do
  let origwidth := grid[0]!.size
  let width := 3 + origwidth * 2
  let bufferRow := (#['*'] ++ (mkArray (width - 2) '·') ++ #['*'])
  let mut out : Array₂ Char := #[mkArray width '*']
  out := out.push bufferRow
  for row in grid do
    out := out.push (puffRow row)
    out := out.push bufferRow
  out := out.push (mkArray width '*')
  return out

partial def dfs (grid : Array₂ Char) (visited : Array₂ Bool)
    (pos : Nat × Nat) (stack : List (Nat × Nat) := []) (count := 0) : Nat :=
  if visited[pos.1]![pos.2]! then
    match stack with
    | [] => count
    | x :: rest => dfs grid visited x rest count
  else
    let newvisited := visited.set₂ pos.1 pos.2 true
    match grid[pos.1]![pos.2]! with
    | '.' =>
      let stackextra := Direction.fold (init := []) fun acc dir =>
        let newpos := pos + dir
        if visited[newpos.1]![newpos.2]! == false then
          newpos :: acc
        else acc
      let newstack := stackextra ++ stack
      match newstack with
      | [] => count
      | x :: rest => dfs grid newvisited x rest (count + 1)
    | '*' => match stack with
           | [] => count
           | x :: rest => dfs grid newvisited x rest count
    | 'M' => match stack with
           | [] => count
           | x :: rest => dfs grid newvisited x rest count
    | '·' =>
      let stackextra := Direction.fold (init := []) fun acc dir =>
        let newpos := pos + dir
        if visited[newpos.1]![newpos.2]! == false then
          newpos :: acc
        else acc
      let newstack := stackextra ++ stack
      match newstack with
      | [] => count
      | x :: rest => dfs grid newvisited x rest  count
    | _ =>
      let stackextra := Direction.fold (init := []) fun acc dir =>
        let newpos := pos + dir
        if visited[newpos.1]![newpos.2]! == false then
          newpos :: acc
        else acc
      let newstack := stackextra ++ stack
      match newstack with
      | [] => count
      | x :: rest => dfs grid newvisited x rest (count + 1)

partial def walkFixGrid (grid : Array₂ Char) (pos : Nat × Nat) (fromDir : Direction) :
    Option (Array₂ Char) := do
  let some dir := next fromDir grid[pos.1]![pos.2]! | failure
  let newpos := pos + dir + dir
  let fixedGrid1 := grid.set₂ (pos + dir).1 (pos + dir).2 'M'
  let fixedGrid2 := fixedGrid1.set₂ pos.1 pos.2 'M'
  if (grid[newpos.1]![newpos.2]! == 'S') then return fixedGrid2
  else return (← walkFixGrid fixedGrid2 newpos dir)

def printGrid (grid : Array₂ Char) : IO Unit := do
  for row in grid do
    IO.println <| row.foldl (init := "") fun acc c => acc.push c

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let grid := puffGrid rawdata
  let n := grid.size
  let m := grid[0]!.size
  let visited := Array.mkArray₂ n m false

  let some startPos := grid.findIdx₂ (fun x => x == 'S') | panic! "Can't find starting point"
  let startDir :: _ := possibleSteps grid startPos true | panic! "No possible starting direction"
  let some fixedGrid := walkFixGrid (grid.set₂ (startPos + startDir).1 (startPos + startDir).2 'M')
    (startPos + startDir + startDir) startDir | panic! "couldn't fix grid"
  let refixedGrid := fixedGrid.set₂ startPos.1 startPos.2 'M'
  --printGrid refixedGrid
  let count1 := dfs refixedGrid visited (startPos + Direction.n + Direction.w)
  let count2 := dfs refixedGrid visited (startPos + Direction.n + Direction.e)
  let count3 := dfs refixedGrid visited (startPos + Direction.s + Direction.w)
  let count4 := dfs refixedGrid visited (startPos + Direction.s + Direction.e)
  return s!"Try these numbers: NW = {count1}, NE = {count2}, SW = {count3}, SE = {count4}"

--#eval secondPart testinput           --(ans: )
--#eval secondPart testinput3           --(ans: )
--#eval secondPart testinput4          --(ans: )
--#eval secondPart testinput5          --(ans: 10)
--#eval secondPart realinput           --(ans: 305)

end Day10
