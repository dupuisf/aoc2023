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

def findNodes (grid : Vec₂ n m Char) : Std.RBMap Pos (List (Pos × Nat)) compare := Id.run do
  let mut out : Std.RBMap Pos (List (Pos × Nat)) compare := Std.RBMap.empty
  out := out.insert ⟨1,1⟩ []   -- start position
  out := out.insert ⟨n-2, m-2⟩ []   -- target position
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
        out := out.insert pos []
  return out

def findNodesDebug (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray
                  |>.toVec₂  | return "Rows not all the same size"
  let out := findNodes grid
  --return s!"{grid.count (· == '.')}"
  return s!"{out.toList}"

--#eval findNodesDebug testinput1
--#eval findNodesDebug realinput

/-- Get the edge that starts at `start` in direction `dir`. Output `none` if that edge is
disallowed, i.e. goes to the edge of the grid in the wrong direction, is a loop, or leads into
a cul-de-sac. Meant to be started not on `start` but right next to it. -/
partial def getEdge (grid : Vec₂ n m Char) (nodes : Std.RBMap Pos (List (Pos × Nat)) compare)
    (start cur : Pos) (prevdir : Direction) (dist := 1) : Option (Pos × Nat) :=
  match nodes.find? cur with
  | none =>
      dbg_trace s!"here, cur = {cur}, prevdir = {prevdir}, dist = {dist}"
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

def getEdgeDebug (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray
                  |>.toVec₂  | return "Rows not all the same size"
  let nodes := findNodes grid
  --let out := getEdge grid nodes ⟨3, 11⟩ ⟨3, 12⟩ .e
  let out := getEdge grid nodes ⟨11, 21⟩ ⟨10, 21⟩ .n
  --return s!"{grid.count (· == '.')}"
  return s!"{out}"

#eval getEdgeDebug testinput1
--#eval getEdgeDebug realinput


structure GraphNode where
  pos : Pos
  neighbors : List (Nat × Nat)  -- ⟨index of neighbor, dist⟩
deriving BEq, Repr, Inhabited

structure GraphBuilderState (n m : Nat) where
  grid : Vec₂ n m Char
  curgraph : Array GraphNode
  lastnode : Nat   -- index in curgraph
  seen : Std.RBSet Pos compare
  target : Pos
  /-- none => bidirectional, false => backwards only, true => forwards only -/
  forwardsOnly : Option Bool
  /-- Distance seen so far in this edge -/
  edgeDist : Nat
  q : Std.Queue Pos
deriving Inhabited

def popQueue₂ : StateM (GraphBuilderState n m) (Option Pos) := do
  let env ← get
  match env.q.dequeue? with
  | none => return none
  | some ⟨pos, q'⟩ =>
      set { env with q := q' }
      return some pos

def makeNode : StateM (GraphBuilderState n m) Unit := do
  sorry

partial def buildGraph : StateM (GraphBuilderState n m) (Array GraphNode) := do
  match (← popQueue₂) with
  | none => return (← get).curgraph
  | some pos =>
      let e ← get
      if pos = e.target then
        makeNode
        buildGraph
      else
        let opendirs : List Direction := Direction.fold (init := [])
          fun acc dir =>
            let newpos := pos + dir
            if (e.grid.get'! ⟨newpos.y, newpos.x⟩ != '#') ∧ !(e.seen.find? newpos).isSome then
              dir :: acc
            else acc
        match opendirs with
        | [] => buildGraph
        | [dir] =>
            let newseen := e.seen.insert pos
            if pos.x = 1 ∧ dir = .n then set { e with forwardsOnly := some false }
            else if pos.x = 1 ∧ dir = .s then set { e with forwardsOnly := some true }
            else if pos.x = m-2 ∧ dir = .n then set { e with forwardsOnly := some false }
            else if pos.x = m-2 ∧ dir = .s then set { e with forwardsOnly := some true }
            else if pos.y = 1 ∧ dir = .w then set { e with forwardsOnly := some false }
            else if pos.y = 1 ∧ dir = .e then set { e with forwardsOnly := some true }
            else if pos.y = 1 ∧ dir = .w then set { e with forwardsOnly := some false }
            else if pos.y = 1 ∧ dir = .e then set { e with forwardsOnly := some true }
            else if pos.y = n-2 ∧ dir = .w then set { e with forwardsOnly := some false }
            else if pos.y = n-2 ∧ dir = .e then set { e with forwardsOnly := some true }
            set { e with seen := newseen, q := e.q.enqueue (pos + dir) }
            buildGraph
        | dirs =>
            sorry



def secondPart (input : FilePath) : IO String := do
  let some ⟨n, m, grid⟩ := (← IO.FS.lines input).map String.toCharArray
                  |>.toVec₂  | return "Rows not all the same size"
  let initst : BFSState n m :=
    { grid := grid
      best := 0
      target := ⟨n-1, m-2⟩
      q := Std.Queue.empty.enqueue ⟨⟨0, 1⟩, Std.RBSet.empty⟩}
  let out := StateT.run' (m := Id) search initst
  --return s!"{grid.count (· == '.')}"
  return s!"{out}"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )


-- 9280 '.' tiles

end Day23
