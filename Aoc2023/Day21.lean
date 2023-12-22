import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day21

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_21_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_21_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_21"

/-
PART 1:
-/

inductive Direction
| n | w | e | s
deriving BEq, Repr, Inhabited, DecidableEq

instance : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"

def stepsDir (pos : Int × Int) (dir : Direction) (steps : Int) : Int × Int :=
  match dir with
  | .n => ⟨pos.1 - steps, pos.2⟩
  | .w => ⟨pos.1, pos.2 - steps⟩
  | .s => ⟨pos.1 + steps, pos.2⟩
  | .e => ⟨pos.1, pos.2 + steps⟩

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

structure BFSState (n m : Nat) where
  grid : Vec₂ n m Char
  seen : Vec₂ n m Bool
  q : Std.BinomialHeap ((Int × Int) × Nat) (fun x y => x.2 ≤ y.2)
  dists : Vec₂ n m (Option Nat)
  curdist : Nat

def popQueue : StateM (BFSState n m) (Option ((Int × Int) × Nat)) := do
  let env ← get
  match env.q.deleteMin with
  | none => return none
  | some ⟨⟨pos, curdist⟩, q'⟩ =>
      set { env with q := q' }
      return some ⟨pos, curdist⟩

partial def bfs (fuel : Nat) : StateM (BFSState n m) (Vec₂ n m (Option Nat)) := do
  --if fuel = 0 then return (← get).dists
  match (← popQueue) with
  | none => return (← get).dists
  | some ⟨pos, curdist⟩ =>
      if pos.1 < n ∧ pos.2 < m then
        match (← get).seen.get'? pos with
        | none => bfs (fuel-1)
        | some true =>
            bfs (fuel-1)
        | some false =>
            let env ← get
            match env.grid.get'? pos with
            | none => bfs (fuel-1)
            | some '#' =>
                set { env with
                      seen := env.seen.set! pos.1.toNat pos.2.toNat true,
                      dists := env.dists.set! pos.1.toNat pos.2.toNat none }
                bfs (fuel-1)
            | _ =>
                set { env with
                      seen := env.seen.set! pos.1.toNat pos.2.toNat true,
                      dists := env.dists.set! pos.1.toNat pos.2.toNat curdist }
                let newq :=
                  Direction.fold (init := env.q) fun acc dir =>
                    acc.insert ⟨(stepsDir pos dir 1), curdist+1⟩
                let env ← get
                set { env with q := newq }
                bfs (fuel-1)
      else bfs (fuel-1)

def printGrid (grid : Vec₂ n m Char) : IO Unit := do
  for hi : i in [0:n] do
    IO.println <| String.ofCharArray grid[i].val

def printGrid' [ToString α] (grid : Vec₂ n m α) : IO Unit := do
  for hi : i in [0:n] do
    IO.println <| grid[i].val.foldl (init := "") fun acc a => acc ++ s!" | {a}"

def count (grid : Vec₂ n m α) (p : α → Bool) : Nat :=
  grid.val.foldtl (init := 0) fun acc c => if p c then acc+1 else acc

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let some start := grid.val.findIdx₂ (· == 'S') | return "Error"
  let initEnv : BFSState n m :=
    { grid := grid
      seen := Vec₂.mkVec₂ n m false
      q := Std.BinomialHeap.empty.insert ⟨⟨(start.1 : Int), (start.2 : Int)⟩, 0⟩
      dists := Vec₂.mkVec₂ n m none,
      curdist := 0 }
  let finalGrid := StateT.run' (bfs 0) initEnv
  let f (x? : Option Nat) : Bool :=
    match x? with
    | none => false
    | some x => x ≤ 64 ∧ x % 2 = 0
  return s!"{count finalGrid f}"

--#eval firstPart testinput1           --(ans: 16 for 6 steps)
--#eval firstPart realinput           --(ans: 3594)  vraie grille 131×131 = 17161 cellules

/-
PART 2:
-/

def getDists (grid : Vec₂ n m Char) (startpos : Int × Int) : Vec₂ n m (Option Nat) :=
  let initEnv : BFSState n m :=
    { grid := grid,
      seen := Vec₂.mkVec₂ n m false,
      q := Std.BinomialHeap.empty.insert ⟨startpos, 0⟩,
      dists := Vec₂.mkVec₂ n m none,
      curdist := 0 }
  StateT.run' (m := Id) (bfs 0) initEnv

def debug2 (input : FilePath) : IO String := do
  let max' : Nat → Option Nat → Nat := fun x y? => match y? with | none => x | some y => max x y
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let some start := grid.val.findIdx₂ (· == 'S') | return "Error"
  let distsBottomLeft := getDists grid ⟨n-1, 0⟩
  let distsBottomMiddle := getDists grid ⟨n-1, n/2⟩
  let distsBottomRight := getDists grid ⟨n-1, m-1⟩
  let distsLeft := getDists grid ⟨n/2, 0⟩
  let distsRight := getDists grid ⟨n/2, m-1⟩
  let distsTopLeft := getDists grid ⟨0, 0⟩
  let distsTopMiddle := getDists grid ⟨0, n/2⟩
  let distsTopRight := getDists grid ⟨0, m-1⟩
  IO.println s!"Bottom left: max dist = {distsBottomLeft.val.foldtl (init := 0) max'}"
  IO.println s!"Bottom middle: max dist = {distsBottomMiddle.val.foldtl (init := 0) max'}"
  IO.println s!"Bottom right: max dist = {distsBottomRight.val.foldtl (init := 0) max'}"
  IO.println s!"Left: max dist = {distsLeft.val.foldtl (init := 0) max'}"
  IO.println s!"Right: max dist = {distsRight.val.foldtl (init := 0) max'}"
  IO.println s!"Top left: max dist = {distsTopLeft.val.foldtl (init := 0) max'}"
  IO.println s!"Top middle: max dist = {distsTopMiddle.val.foldtl (init := 0) max'}"
  IO.println s!"Top right: max dist = {distsTopRight.val.foldtl (init := 0) max'}"
  return "bla"

def debug3 (input : FilePath) : IO String := do
  let f (d : Nat) (x? : Option Nat) : Bool :=
    match x? with
    | none => false
    | some x => x ≤ d ∧ x % 2 = 1
  let max' : Nat → Option Nat → Nat := fun x y? => match y? with | none => x | some y => max x y
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let some start := grid.val.findIdx₂ (· == 'S') | return "Error"
  let bl := getDists grid ⟨n-1, 0⟩
  --let bm := getDists grid ⟨n-1, n/2⟩
  --let br := getDists grid ⟨n-1, m-1⟩
  let l := getDists grid ⟨n/2, 0⟩
  let r := getDists grid ⟨n/2, m-1⟩
  let tl := getDists grid ⟨0, 0⟩
  --let tm := getDists grid ⟨0, n/2⟩
  --let tr := getDists grid ⟨0, m-1⟩
  IO.println s!"Bottom left: count = {count bl (f 327)}"
  --IO.println s!"Bottom middle: max dist = {count bm (f 196)}"
  --IO.println s!"Bottom right: max dist = {count br (f 196)}"
  --IO.println s!"Left: count = {count l (f (2*131))}"
  --IO.println s!"Right: count = {count r (f (2*131))}"
  IO.println s!"Top left: max dist = {count tl (f 327)}"
  --IO.println s!"Top middle: max dist = {count tm (f 196)}"
  --IO.println s!"Top right: max dist = {count tr (f 196)}"
  return "bla"

def debug4 (input : FilePath) : IO String := do
  let f (x? : Option Nat) : Bool :=
    match x? with
    | none => false
    | some x => x % 2 = 0
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let some start := grid.val.findIdx₂ (· == 'S') | return "Error"
  --let dists := getDists grid ⟨start.1, start.2⟩
  let dists := getDists grid ⟨65, 0⟩
  return s!"{count dists f}"

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let some start := grid.val.findIdx₂ (· == 'S') | return "Error"
  return s!"{start}"

--#eval debug2 testinput1           --(ans: )
--#eval debug2 realinput           --(ans: )
#eval debug3 realinput           --(ans: )
--#eval debug4 realinput           --(ans: )
--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

/- Real grid:
131×131, 14789 accessible cells in total, 8 inaccessible cells
7401 odd accessible, 7388 even accessible
- whole border has no rocks, both central axes have no rocks either
- Start pos : 65, 65

-/


end Day21
