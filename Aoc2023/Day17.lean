import Aoc2023.Utils
import Std.Data.BinomialHeap.Basic

open System Lean Lean.Parsec

namespace Day17

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_17_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_17_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_17"

/-
PART 1:
-/

inductive Direction
| n | w | e | s
deriving BEq, Repr, DecidableEq

instance : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"

instance : HAdd (Int × Int) Direction (Int × Int) where
  hAdd x y := match y with
              | .n => ⟨x.1-1, x.2⟩ | .w => ⟨x.1, x.2 - 1⟩ | .e => ⟨x.1, x.2 + 1⟩ | .s => ⟨x.1+1, x.2⟩

/-- Possible state for each cell: for each direction, number of steps taken
in that direction so far -/
structure State where
  n : Vec 3 Bool
  w : Vec 3 Bool
  s : Vec 3 Bool
  e : Vec 3 Bool

structure QueueElem where
  x : Int
  y : Int
  dir : Direction
  steps : Nat
  cost : Nat
deriving BEq, DecidableEq

def State.incl (st : State) (cur : QueueElem) : Bool :=
  match cur.dir with
  | .n => st.n[cur.steps]!
  | .w => st.w[cur.steps]!
  | .s => st.s[cur.steps]!
  | .e => st.e[cur.steps]!

instance : LE QueueElem where
  le a b := a.cost ≤ b.cost

instance : DecidableRel (α := QueueElem) (· ≤ ·) := fun a b =>
  match h : decide (a.cost ≤ b.cost) with
  | false => .isFalse (by rwa [decide_eq_false_iff_not] at h)
  | true => .isTrue (by rwa [decide_eq_true_iff] at h)

def getNeighbors (grid : Vec₂ n m Nat) (cur : QueueElem) : List QueueElem := sorry

open Std in
partial def dijkstra (grid : Vec₂ n m Nat) (seen : Vec₂ n m State)
    (q : BinomialHeap QueueElem (· ≤ ·)) : Option Nat :=
  match q.deleteMin with
  | none => none
  | some ⟨cur, q'⟩ =>
    if cur.x == n-1 ∧ cur.y == m-1 then some cur.cost
    else
      match seen.get? cur.x cur.y with
      | none => none -- out of bounds: should never happen
      | some st =>
        if st.incl cur then dijkstra grid seen q'   -- we've been here before
        else
          let neighbors := getNeighbors grid cur
          sorry


def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input).map String.toCharArray
                  |>.map (·.map fun c => c.toNat - 48)
  let some ⟨n, m, grid⟩ := rawdata.toVec₂ | return "Rows not all the same size"
  return s!"bla"

--#eval firstPart testinput1           --(ans: 102)
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day17
