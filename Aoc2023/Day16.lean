import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day16

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_16_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_16_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_16"

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

def Direction.CW : Direction → Direction
| .n => .e | .w => .n | .e => .s | .s => .w

def Direction.CCW : Direction → Direction
| .n => .w | .w => .s | .e => .n | .s => .e

def Direction.slash : Direction → Direction
| .n => .e | .w => .s | .e => .n | .s => .w

def Direction.backslash : Direction → Direction
| .n => .w | .w => .n | .e => .s | .s => .e

def Direction.vertbar : Direction → List Direction
| .n => [.n] | .w => [.n, .s] | .e => [.n, .s] | .s => [.s]

def Direction.dash : Direction → List Direction
| .n => [.e, .w] | .w => [.w] | .e => [.e] | .s => [.e, .w]

def Direction.next : Char → Direction → List Direction
| '.', d => [d]
| '/', d => [d.slash]
| '\\', d => [d.backslash]
| '-', d => d.dash
| '|', d => d.vertbar
| _, _ => []

def setSeen (c : Bool × Bool × Bool × Bool) (dir : Direction) : Bool × Bool × Bool × Bool :=
  match dir with
  | .n => ⟨true, c.2.1, c.2.2.1, c.2.2.2⟩
  | .w => ⟨c.1, true, c.2.2.1, c.2.2.2⟩
  | .s => ⟨c.1, c.2.1, true, c.2.2.2⟩
  | .e => ⟨c.1, c.2.1, c.2.2.1, true⟩

def getSeen (c : Bool × Bool × Bool × Bool) (dir : Direction) : Bool :=
  match dir with
  | .n => c.1
  | .w => c.2.1
  | .s => c.2.2.1
  | .e => c.2.2.2

def seenAny (s : Bool × Bool × Bool × Bool) : Bool := Id.run do
  if s.1 then return true
  if s.2.1 then return true
  if s.2.2.1 then return true
  if s.2.2.2 then return true
  return false

def printSeen (seen : Vec₂ n m (Bool × Bool × Bool × Bool)) : IO Unit := do
  for hi: i in [0:n] do
    let mut row : String := ""
    for hj : j in [0:m] do
      let c := if seenAny seen[i][j] then '*' else '.'
      row := row.push c
    IO.println row

/- `seen[i][j] = ⟨n, w, s, e⟩` tells us if cell i,j has been visited while going N, W, S, E at the
time of entering the cell. -/
partial def bfs (grid : Vec₂ n m Char) (seen : Vec₂ n m (Bool × Bool × Bool × Bool))
    (q : Std.Queue (Nat × Nat × Direction)) : Vec₂ n m (Bool × Bool × Bool × Bool) :=
  match q.dequeue? with
  | none => seen
  | some ⟨⟨i, j, dir⟩, newq⟩ =>
      if getSeen seen[i]![j]! dir then
        bfs grid seen newq
      else
        let newseen := seen.set! i j (setSeen seen[i]![j]! dir)
        let q' := (dir.next grid[i]![j]!).foldl (init := newq) fun acc d =>
          let (⟨i', j'⟩ : Nat × Nat) := (⟨i, j⟩ : Nat × Nat) + d
          acc.enqueue ⟨i', j', d⟩
        bfs grid newseen q'

def countEnergy (seen : Vec₂ n m (Bool × Bool × Bool × Bool)) : Nat := Id.run do
  let as := seen.val
  let mut cnt := 0
  for i in [1:n-1] do
    for j in [1:m-1] do
      if seenAny as[i]![j]! then cnt := cnt+1
  return cnt

def debug1 (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray |>.addWall '#' |>.toVec₂
    | return "Rows not all the same size"
  let initseen : Vec₂ n m (Bool × Bool × Bool × Bool) := Vec₂.mkVec₂ n m ⟨false, false, false, false⟩
  let initqueue := Std.Queue.empty.enqueue (⟨1, 1, .e⟩ : Nat × Nat × Direction)
  let out := bfs grid initseen initqueue
  printSeen out
  return s!"{countEnergy out}"

def firstPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray |>.addWall '#' |>.toVec₂
    | return "Rows not all the same size"
  let initseen : Vec₂ n m (Bool × Bool × Bool × Bool) := Vec₂.mkVec₂ n m ⟨false, false, false, false⟩
  let initqueue := Std.Queue.empty.enqueue (⟨1, 1, .e⟩ : Nat × Nat × Direction)
  let out := bfs grid initseen initqueue
  return s!"{countEnergy out}"

--#eval firstPart testinput1           --(ans: )
--#eval debug1 testinput1           --(ans: )
--#eval firstPart realinput           --(ans: 8539)

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray |>.addWall '#' |>.toVec₂
    | return "Rows not all the same size"
  let initseen : Vec₂ n m (Bool × Bool × Bool × Bool) :=
    Vec₂.mkVec₂ n m ⟨false, false, false, false⟩
  -- North wall
  let mut best := 0
  for i in [1:n-1] do
    let initqueue := Std.Queue.empty.enqueue (⟨1, i, .s⟩ : Nat × Nat × Direction)
    let out := bfs grid initseen initqueue
    let e := countEnergy out
    best := max best e
  -- West wall
  for i in [1:m-1] do
    let initqueue := Std.Queue.empty.enqueue (⟨i, 1, .e⟩ : Nat × Nat × Direction)
    let out := bfs grid initseen initqueue
    let e := countEnergy out
    best := max best e
  -- East wall
  for i in [1:m-1] do
    let initqueue := Std.Queue.empty.enqueue (⟨i, m-2, .w⟩ : Nat × Nat × Direction)
    let out := bfs grid initseen initqueue
    let e := countEnergy out
    best := max best e
  -- South wall
  for i in [1:n-1] do
    let initqueue := Std.Queue.empty.enqueue (⟨n-2, i, .n⟩ : Nat × Nat × Direction)
    let out := bfs grid initseen initqueue
    let e := countEnergy out
    best := max best e
  return s!"{best}"

--#eval secondPart testinput1           --(ans: )
--#eval debug2 testinput1           --(ans: )
--#eval secondPart realinput           --(ans: 8674)

end Day16
