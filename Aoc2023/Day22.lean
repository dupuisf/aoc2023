import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day22

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_22_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_22_test2"
def testinput3 : FilePath := "/home/fred/lean/aoc2023/input_22_test3"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_22"

/-
PART 1:
-/

macro "derive_ToString" t:term : command =>
  `(instance : ToString $t where toString := Std.Format.pretty ∘ repr)

structure Pos where
  x : Int
  y : Int
  z : Int
deriving BEq, Repr, DecidableEq, Inhabited

structure Brick where
  end1 : Pos
  end2 : Pos
deriving BEq, Repr, DecidableEq, Inhabited

derive_ToString Pos

instance : ToString Brick where
  toString b := s!"({b.end1.x}, {b.end1.y}, {b.end1.z}) ~ ({b.end2.x}, {b.end2.y}, {b.end2.z})"

instance : HAdd Pos Int Pos where
  hAdd p n := ⟨p.x, p.y, p.z + n⟩

instance : HSub Pos Int Pos where
  hSub p n := ⟨p.x, p.y, p.z - n⟩

instance : HAdd Brick Int Brick where
  hAdd b n := { end1 := b.end1 + n
                end2 := b.end2 + n }

instance : HSub Brick Int Brick where
  hSub b n := { end1 := b.end1 - n
                end2 := b.end2 - n }

def Brick.top (b : Brick) : Int := max b.end1.z b.end2.z
def Brick.bottom (b : Brick) : Int := min b.end1.z b.end2.z
def Brick.xhi (b : Brick) : Int := max b.end1.x b.end2.x
def Brick.xlo (b : Brick) : Int := min b.end1.x b.end2.x
def Brick.yhi (b : Brick) : Int := max b.end1.y b.end2.y
def Brick.ylo (b : Brick) : Int := min b.end1.y b.end2.y

def Brick.intersect (b₁ b₂ : Brick) : Bool := Id.run do
  if b₁.xhi < b₂.xlo then return false
  if b₂.xhi < b₁.xlo then return false
  if b₁.yhi < b₂.ylo then return false
  if b₂.yhi < b₁.ylo then return false
  return true

def parseBrick : Parsec Brick := do
  let x₁ ← natNum
  skipString ","
  let y₁ ← natNum
  skipString ","
  let z₁ ← natNum
  skipString "~"
  let x₂ ← natNum
  skipString ","
  let y₂ ← natNum
  skipString ","
  let z₂ ← natNum
  return ⟨⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩⟩

def printBricks (bs : Array Brick) : IO Unit := do
  for b in bs.reverse do
    IO.println b

-- True if b₁ supports brick b₂ (maybe not sole supporting brick)
def Brick.supports (b₁ b₂ : Brick) : Bool :=
  if b₁.top + 1 ≠ b₂.bottom then false
  else b₁.intersect b₂

def pullDown (bricks : Array Brick) (i j : Nat) : Array Brick := Id.run do
  let mut out := bricks
  if 0 < j then
    if out[i]!.bottom ≤ out[j-1]!.top then pullDown out i (j-1)
    else
      let curdiff := out[i]!.bottom - (out[j-1]!.top + 1)
      out := out.set! i (out[i]! - curdiff)
      if out[j-1]!.intersect out[i]! then
        -- Found resting place for the block
        return out
      else
        -- Keep going down
        pullDown out i (j-1)
  else
    -- Block i hits rock bottom
    let curdiff := out[i]!.bottom - 1
    return (out.set! i (out[i]! - curdiff))

def pushDown (bricks : Array Brick) (i : Nat) : Array Brick := Id.run do
  let mut out := bricks
  for j' in [1:i+1] do
    let j := i - j'
    if out[j]!.top > out[j+1]!.top then
      out := out.swap! j (j+1)
  return out

def pushDownAll (bricks : Array Brick) : Array Brick :=
  Nat.fold (n := bricks.size) (init := bricks) fun i br =>
    pushDown (pullDown br i i) i

def findSupporting (bricks : Array Brick) (i : Nat) : Option Nat := Id.run do
  let mut acc : Nat := 0
  let mut first := i-1
  for j' in [1:i+1] do
    let j := i - j'
    if bricks[j]!.top < bricks[i]!.bottom - 1 then
      if acc = 1 then return some first else return none
    if bricks[j]!.supports bricks[i]! then
      acc := acc+1
      first := j
  if acc = 1 then return some first else return none

def findAllSupporting (bricks : Array Brick) (i : Nat) : List Nat := Id.run do
  let mut acc : List Nat := []
  for j' in [1:i+1] do
    let j := i - j'
    if bricks[j]!.top < bricks[i]!.bottom - 1 then
      return acc
    if bricks[j]!.supports bricks[i]! then
      acc := j :: acc
  return acc

def findAllSupported (bricks : Array Brick) (i : Nat) : List Nat := Id.run do
  let n := bricks.size
  let mut acc : List Nat := []
  for j in [i+1:n] do
    if bricks[i]!.supports bricks[j]! then
      acc := j :: acc
  return acc

def markSupporting (bricks : Array Brick) : Array Bool :=
  let n := bricks.size
  Nat.fold (n := n) (init := Array.mkArray n false) fun i acc =>
    match findSupporting bricks i with
    | none => acc
    | some j => acc.set! j true

def countSupporting (bricks : Array Brick) : Nat :=
  (markSupporting bricks).count id

def firstPart (input : FilePath) : IO String := do
  let some bricksUnsorted := (← IO.FS.lines input).mapM (fun s => String.parse? s parseBrick)
    | return "Parse error"
  let rawbricks := bricksUnsorted.qsort (fun b₁ b₂ => b₁.top < b₂.top)
  let bricks := pushDownAll rawbricks
  return s!"{bricks.size - countSupporting bricks}"

--#eval firstPart testinput1           --(ans: 5)
--#eval firstPart testinput2
--#eval firstPart testinput3
--#eval firstPart realinput           --(ans: 477)   -- 1457 bricks in total

/-
PART 2:
-/

def iAmFalling (supporting : List Nat) (falling : Array Bool) : Bool :=
  supporting.foldl (init := true) fun acc i => acc && falling[i]!

structure BFSState where
  bricks : Array Brick
  supported : Array (List Nat)
  supporting : Array (List Nat)
  falling : Array Bool
  q : Std.BinomialHeap (Nat × Brick) (fun b₁ b₂ => b₁.2.top ≤ b₂.2.top)

def popQueue : StateM BFSState (Option (Nat × Brick)) := do
  let env ← get
  match env.q.deleteMin with
  | none => return none
  | some ⟨⟨idx, b⟩, q'⟩ =>
      set { env with q := q' }
      return some ⟨idx, b⟩

partial def bfs (fuel := 0) (start := true) : StateM BFSState (Array Bool) := do
  --if fuel = 0 then return (← get).dists
  match (← popQueue) with
  | none => return (← get).falling
  | some ⟨idx, _⟩ =>
      let e ← get
      if iAmFalling e.supporting[idx]! e.falling || start then
        let enqueued : List (Nat × Brick) :=
          e.supported[idx]!.foldl (init := []) fun acc i => ⟨i, e.bricks[i]!⟩ :: acc
        set { e with
              falling := e.falling.set! idx true
              q := enqueued.foldl (init := e.q) fun acc elem => acc.insert elem }
        bfs (fuel - 1) false
      else bfs (fuel-1) false

def findFalling (bricks : Array Brick) (supporting supported : Array (List Nat)) (i : Nat) : Array Bool :=
  let initEnv : BFSState :=
    { bricks := bricks
      supported := supported
      supporting := supporting
      falling := (Array.mkArray bricks.size false).set! i true
      q := Std.BinomialHeap.empty.insert ⟨i, bricks[i]!⟩ }
  StateT.run' (m := Id) (bfs 0) initEnv

def countFalling (bricks : Array Brick) (supporting supported : Array (List Nat)) (i : Nat) : Nat :=
  let falling := findFalling bricks supporting supported i
  (falling.count id) - 1

def secondPart (input : FilePath) : IO String := do
  let some bricksUnsorted := (← IO.FS.lines input).mapM (fun s => String.parse? s parseBrick)
    | return "Parse error"
  let rawbricks := bricksUnsorted.qsort (fun b₁ b₂ => b₁.top < b₂.top)
  let bricks := pushDownAll rawbricks
  let supporting := bricks.mapIdx (fun i _ => findAllSupporting bricks i)
  let supported := bricks.mapIdx (fun i _ => findAllSupported bricks i)
  let mut total := 0
  for i in [0:bricks.size] do
    total := total + countFalling bricks supporting supported i
  return s!"{total}"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day22
