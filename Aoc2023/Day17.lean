import Aoc2023.Utils
import Aoc2023.Direction
import Std.Data.BinomialHeap.Basic

open System Lean Lean.Parsec

namespace Day17

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_17_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_17_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_17"

/-
PART 1:
-/

/-- Possible state for each cell: for each direction, number of steps taken
in that direction so far. Coded in binary -/
structure State where
  n : Nat
  w : Nat
  s : Nat
  e : Nat
deriving BEq, Inhabited

structure QueueElem where
  pos : Int × Int
  dir : Direction
  steps : Nat
  cost : Nat
deriving BEq, DecidableEq

def State.incl (st : State) (cur : QueueElem) : Bool :=
  match cur.dir with
  | .n => (st.n &&& 2^cur.steps) != 0
  | .w => (st.w &&& 2^cur.steps) != 0
  | .s => (st.s &&& 2^cur.steps) != 0
  | .e => (st.e &&& 2^cur.steps) != 0

def State.set (st : State) (cur : QueueElem) : State :=
  match cur.dir with
  | .n => ⟨st.n ||| 2^cur.steps, st.w, st.s, st.e⟩
  | .w => ⟨st.n, st.w ||| 2^cur.steps, st.s, st.e⟩
  | .s => ⟨st.n, st.w, st.s ||| 2^cur.steps, st.e⟩
  | .e => ⟨st.n, st.w, st.s, st.e ||| 2^cur.steps⟩

instance : LE QueueElem where
  le a b := a.cost ≤ b.cost

instance : DecidableRel (α := QueueElem) (· ≤ ·) := fun a b =>
  match h : decide (a.cost ≤ b.cost) with
  | false => .isFalse (by rwa [decide_eq_false_iff_not] at h)
  | true => .isTrue (by rwa [decide_eq_true_iff] at h)

def getNeighbors₁ (grid : Vec₂ n m Nat) (cur : QueueElem) : List QueueElem :=
  let front : List QueueElem :=
    if cur.steps = 3 then []
    else
      match grid.get'? (cur.pos + cur.dir) with
      | none => []
      | some cost => [⟨cur.pos + cur.dir, cur.dir, cur.steps+1, cur.cost + cost⟩]
  let left : List QueueElem :=
    match grid.get'? (cur.pos + cur.dir.left) with
    | none => []
    | some cost => [⟨cur.pos + cur.dir.left, cur.dir.left, 1, cur.cost + cost⟩]
  let right : List QueueElem :=
    match grid.get'? (cur.pos + cur.dir.right) with
    | none => []
    | some cost => [⟨cur.pos + cur.dir.right, cur.dir.right, 1, cur.cost + cost⟩]
  front ++ left ++ right

def setSeen (seen : Vec₂ n m State) (cur : QueueElem) : Vec₂ n m State :=
  let st? := seen.get? cur.pos.1 cur.pos.2
  match st? with
  | none => panic! "oh no"
  | some st =>
    seen.set! cur.pos.1.toNat cur.pos.2.toNat (st.set cur)

open Std in
partial def dijkstra (grid : Vec₂ n m Nat) (seen : Vec₂ n m State)
    (q : BinomialHeap QueueElem (· ≤ ·))
    (getNeighbors : Vec₂ n m Nat → QueueElem → List QueueElem)
    (stopThreshold := 0) : Option Nat :=
  match q.deleteMin with
  | none => none     -- Queue is empty without finding the target
  | some ⟨cur, q'⟩ =>
    if (cur.pos == ⟨n-1, m-1⟩) ∧ (cur.steps ≥ stopThreshold) then some cur.cost   -- Victory!
    else
      match seen.get'? cur.pos with
      | none => none -- out of bounds: should never happen
      | some st =>
        if st.incl cur then dijkstra grid seen q' getNeighbors stopThreshold -- we've been here before: do nothing
        else
          let neighbors := getNeighbors grid cur
          -- Enqueue all the neighbors
          let newq := neighbors.foldl (init := q') fun acc qe => acc.insert qe
          let newseen := setSeen seen cur    -- mark current node as visited
          dijkstra grid newseen newq getNeighbors stopThreshold

open Std in
def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
                  |>.map (·.map fun c => c.toNat - 48)
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let initseen : Vec₂ n m State := Vec₂.mkVec₂ n m ⟨0,0,0,0⟩
  let mut initq : BinomialHeap QueueElem (· ≤ ·) := BinomialHeap.empty
  initq := initq.insert ⟨⟨0, 0⟩, .e, 0, 0⟩
  initq := initq.insert ⟨⟨0, 0⟩, .s, 0, 0⟩
  let some out := dijkstra grid initseen initq getNeighbors₁ | return "Couldn't find target"
  return s!"{out}"

--#eval firstPart testinput1           --(ans: 102)
--#eval firstPart realinput           --(ans: 1263)

/-
PART 2:
-/

def getNeighbors₂ (grid : Vec₂ n m Nat) (cur : QueueElem) : List QueueElem :=
  let front : List QueueElem :=
    if cur.steps = 10 then []
    else
      match grid.get'? (cur.pos + cur.dir) with
      | none => []
      | some cost => [⟨cur.pos + cur.dir, cur.dir, cur.steps+1, cur.cost + cost⟩]
  let left : List QueueElem :=
    if cur.steps < 4 then []
    else
      match grid.get'? (cur.pos + cur.dir.left) with
      | none => []
      | some cost => [⟨cur.pos + cur.dir.left, cur.dir.left, 1, cur.cost + cost⟩]
  let right : List QueueElem :=
    if cur.steps < 4 then []
    else
      match grid.get'? (cur.pos + cur.dir.right) with
      | none => []
      | some cost => [⟨cur.pos + cur.dir.right, cur.dir.right, 1, cur.cost + cost⟩]
  front ++ left ++ right

open Std in
def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
                  |>.map (·.map fun c => c.toNat - 48)
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  let initseen : Vec₂ n m State := Vec₂.mkVec₂ n m ⟨0,0,0,0⟩
  let mut initq : BinomialHeap QueueElem (· ≤ ·) := BinomialHeap.empty
  initq := initq.insert ⟨⟨0, 0⟩, .e, 0, 0⟩
  initq := initq.insert ⟨⟨0, 0⟩, .s, 0, 0⟩
  let some out := dijkstra grid initseen initq getNeighbors₂ 4 | return "Couldn't find target"
  return s!"{out}"

--#eval secondPart testinput1           --(ans: 94)
--#eval secondPart testinput2           --(ans: 71)
--#eval secondPart realinput           --(ans: 1411)

end Day17
