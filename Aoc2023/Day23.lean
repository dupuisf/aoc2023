import Aoc2023.Utils
import Std.Data.RBMap.Basic

open System Lean Lean.Parsec

namespace Day23

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_23_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_23_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_23"

/-
PART 1:
-/

structure Pos where
  y : Int
  x : Int
deriving BEq, Repr, DecidableEq, Inhabited

instance : ToString Pos where
  toString p := s!"⟨{p.y}, {p.x}⟩"

instance : Add Pos where
  add p q := ⟨p.y + q.y, p.x + q.x⟩

instance : Ord Pos where
  compare p1 p2 := match compare p1.1 p2.1 with
    | .eq => compare p1.2 p2.2
    | o   => o

inductive Direction
| n | w | e | s
deriving BEq, Repr, Inhabited, DecidableEq

instance : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"

def stepsDir (pos : Pos) (dir : Direction) (steps : Int) : Pos :=
  match dir with
  | .n => ⟨pos.1 - steps, pos.2⟩
  | .w => ⟨pos.1, pos.2 - steps⟩
  | .s => ⟨pos.1 + steps, pos.2⟩
  | .e => ⟨pos.1, pos.2 + steps⟩

instance : HAdd Pos Direction Pos where
  hAdd pos dir := stepsDir pos dir 1

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

structure BFSState (n m : Nat) where
  grid : Vec₂ n m Char
  best : Nat
  target : Pos
  q : Std.Queue (Pos × Std.RBSet Pos compare)

def popQueue : StateM (BFSState n m) (Option (Pos × Std.RBSet Pos compare)) := do
  let env ← get
  match env.q.dequeue? with
  | none => return none
  | some ⟨⟨pos, path⟩, q'⟩ =>
      set { env with q := q' }
      return some ⟨pos, path⟩

partial def search (fuel := 100) : StateM (BFSState n m) Nat := do
  --if fuel = 0 then return (← get).best
  match (← popQueue) with
  | none => return (← get).best
  | some ⟨pos, path⟩ =>
      --dbg_trace s!"here: pos = {pos}"
      let e ← get
      if pos = e.target then
        if path.size > e.best then
          set { e with best := path.size }
        search (fuel-1)
      else
        match path.find? pos with
        | none =>
          let grid := e.grid
          let newpath := path.insert pos
          match grid.get? pos.y pos.x with
          | none => search (fuel-1)  -- off the grid
          | some '#' => search (fuel-1)  -- into a wall
          | some '^' =>
              let newqelem : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .n 1, newpath⟩
              set { e with q := e.q.enqueue newqelem }
              search (fuel-1)
          | some '>' =>
              let newqelem : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .e 1, newpath⟩
              set { e with q := e.q.enqueue newqelem }
              search (fuel-1)
          | some '<' =>
              let newqelem : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .w 1, newpath⟩
              set { e with q := e.q.enqueue newqelem }
              search (fuel-1)
          | some 'v' =>
              let newqelem : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .s 1, newpath⟩
              set { e with q := e.q.enqueue newqelem }
              search (fuel-1)
          | _ =>
              let north : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .n 1, newpath⟩
              let south : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .s 1, newpath⟩
              let east : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .e 1, newpath⟩
              let west : Pos × Std.RBSet Pos compare :=
                ⟨stepsDir pos .w 1, newpath⟩
              set { e with q := e.q.enqueueAll [north, south, east, west] }
              search (fuel-1)
        | some _ => search (fuel-1)

/-- Works only on modified input where we wall off the entrance and exit and start inside. -/
def firstPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray
                  |>.toVec₂  | return "Rows not all the same size"
  let initst : BFSState n m :=
    { grid := grid
      best := 0
      target := ⟨n-2, m-2⟩
      q := Std.Queue.empty.enqueue ⟨⟨1, 1⟩, Std.RBSet.empty⟩}
  let out : Nat := StateT.run' (m := Id) search initst
  return s!"{out+2}"

--#eval firstPart testinput1           --(ans: 94)
--#eval firstPart realinput           --(ans: 2034)

/-
PART 2:
-/

def findNodes (grid : Vec₂ n m Char) : Std.RBSet Pos compare := Id.run do
  let mut out : Std.RBSet Pos compare := Std.RBSet.empty
  out := out.insert ⟨1,1⟩   -- start position
  out := out.insert ⟨n-2, m-2⟩   -- target position
  for i in [1:n-1] do
    for j in [1:m-1] do
      let pos : Pos := ⟨i, j⟩
      let opendirs : List Direction := Direction.fold (init := [])
        fun acc dir =>
          let newpos := pos + dir
          if (grid.get'! ⟨pos.y, pos.x⟩ != '#') ∧ (grid.get'! ⟨newpos.y, newpos.x⟩ != '#') then
            dir :: acc
          else acc
      if opendirs.length > 2 then
        out := out.insert pos
  return out

/-- Get the edge that starts at `start` in direction `dir`. Output `none` if that edge is
disallowed, i.e. goes to the edge of the grid in the wrong direction, is a loop, or leads into
a cul-de-sac. Meant to be started not on `start` but right next to it. -/
partial def getEdge (grid : Vec₂ n m Char) (nodes : Std.RBSet Pos compare)
    (start cur : Pos) (prevdir : Direction) (dist := 1) : Option (Pos × Nat) :=
  match nodes.find? cur with
  | none =>
      -- not there yet
      let opendirs : List Direction := Direction.fold (init := [])
        fun acc dir =>
          let newpos := cur + dir
          if grid.get'! ⟨newpos.y, newpos.x⟩ != '#' then
            dir :: acc
          else acc
      match opendirs.filter (· != prevdir.flip) with
      | [] => none   -- cul de sac => useless
      | [newdir] =>
          if cur.x = 1 ∧ newdir = .n then none   -- left wall going north
          else if cur.x = m-2 ∧ newdir = .n then none -- right wall going north
          else if cur.y = 1 ∧ newdir = .w then none -- top wall going west
          else if cur.y = n-2 ∧ newdir = .w then none  -- south wall going west
          else getEdge grid nodes start (cur + newdir) newdir (dist + 1)
      | _ => panic! "WTF: unknown node!"
  | some _ =>
      if cur = start then
        none  -- found a self-loop => useless
      else
        some ⟨cur, dist⟩

def getEdges (grid : Vec₂ n m Char) (nodes : Std.RBSet Pos compare) :
    Std.RBMap Pos (List (Pos × Nat)) compare :=
  nodes.foldl (init := Std.RBMap.empty) fun rbmap pos =>
    let startpoints : List (Pos × Direction) :=
      Direction.fold (init := []) fun acc dir =>
        let newpos := pos + dir
        if grid.get'! ⟨newpos.y, newpos.x⟩ != '#' then
          ⟨newpos, dir⟩ :: acc
        else acc
    let edges : List (Pos × Nat) := startpoints.foldl (init := []) fun acc startpoint =>
      let edge := getEdge grid nodes pos startpoint.1 startpoint.2
      match edge with
      | none => acc
      | some x => x :: acc
    rbmap.insert pos edges

structure GraphState where
  graph : Std.RBMap Pos (List (Pos × Nat)) compare
  target : Pos
deriving Inhabited

partial def dfs (pos : Pos) (dist : Nat) (path : Std.RBSet Pos compare) :
    StateM GraphState (Option Nat) := do
  let e ← get
  if pos = e.target then return some dist
  else
    match path.find? pos with
    | none =>
        let edges := e.graph.find! pos
        let best ← edges.foldlM (init := 0) fun acc edge => do
          let curtry ← dfs edge.1 (dist + edge.2) (path.insert pos)
          match curtry with
          | none => return acc
          | some value => if value > acc then return value else return acc
        return best
    | some _ => return none

def secondPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray
                  |>.toVec₂  | return "Rows not all the same size"
  let nodes := findNodes grid
  let graph := getEdges grid nodes
  let initst : GraphState :=
    { graph := graph
      target := ⟨n-2, m-2⟩ }
  let some out := StateT.run' (m := Id) (dfs ⟨1, 1⟩ 2 Std.RBSet.empty) initst
    | return "WTF"
  return s!"{out}"

--#eval secondPart testinput1           --(ans: 154)
--#eval secondPart realinput           --(ans: 6302)


end Day23
