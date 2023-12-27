import Aoc2023.Utils
import Std.Data.RBMap.Basic

open System Lean Lean.Parsec

namespace Day25

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_25_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_25_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_25"

/-
PART 1:
-/

def parseDevice : Parsec (String × List String) := do
  let devname ← word
  skipString ": "
  let devlist ← sepBy word ws
  return ⟨devname, devlist⟩

structure KargerState where
  edges : Array (String × String)
  comps : Std.HashMap String (Option String)  -- none means set representative
  rng : StdGen

abbrev KargerM := OptionT (StateM KargerState)

def KargerM.rand (n : Nat) : KargerM Nat := do
  let env ← get
  let ⟨i, rng'⟩ := randNat env.rng 0 n
  set { env with rng := rng' }
  return i

def numComps : KargerM Nat := do
  let comps := (← get).comps
  let lst := comps.toList.map (fun x => x.1)
  return lst.eraseDup.length

partial def getComp (v : String) : KargerM String := do
  let comps := (← get).comps
  match comps.find? v with
  | none => failure
  | some none => return v
  | some (some x) => getComp x

def setComp (v : String) (new : String) : KargerM Unit := do
  let w ← getComp v
  let e ← get
  set { e with comps := e.comps.modify w (fun _ _ => new) }

def mergeNodes (v₁ v₂ : String) : KargerM Unit := do
  let w₁ ← getComp v₁
  let w₂ ← getComp v₂
  if w₁ == w₂ then failure
  else
    setComp w₂ w₁

def deleteEdge (i : Nat) : KargerM Unit := do
  let env ← get
  set { env with edges := env.edges.eraseIdx i }

partial def karger : KargerM Unit := do
  let rec go (left : Nat) : KargerM Unit := do
    if left = 0 then return
    else
      let env ← get
      let i ← KargerM.rand (env.edges.size - 1)
      let edge := env.edges[i]!
      if (← getComp edge.1) == (← getComp edge.2) then
        deleteEdge i
        go left
      else
        mergeNodes edge.1 edge.2
        go (left-1)
  go ((← numComps) - 2)

def getFinalComp : KargerM (Std.RBSet String compare) := do
  karger
  let e ← get
  let nodeList := e.comps.toList.map (fun z => z.1)
  let reps ← nodeList.mapM (fun z => do return (← getComp z))
  let reps' := reps.eraseDup
  match reps' with
  | [w₁, _] =>
      let lst ← nodeList.filterM (m := KargerM) (fun z => do return (← getComp z) == w₁)
      let rbset : Std.RBSet String compare := Std.RBSet.ofList lst compare
      return rbset
  | _ => failure

def countEdgesAcross (cut : Std.RBSet String compare) (edges : Array (String × String)) : Nat :=
  edges.foldl (init := 0) fun acc ⟨v₁, v₂⟩ =>
    match cut.find? v₁, cut.find? v₂ with
    | none, some _ => acc+1
    | some _, none => acc+1
    | none, none => acc
    | some _, some _ => acc

def KargerM.runKarger (env : KargerState) : Option (Std.RBSet String compare) :=
  StateT.run' (m := Id) (OptionT.run getFinalComp) env

def KargerM.run (f : KargerM α) (env : KargerState) : Option α :=
  StateT.run' (m := Id) (OptionT.run f) env

def KargerM.debugrun [ToString α] (f : KargerM α) (env : KargerState) : IO Unit := do
  let ⟨out, env⟩ := StateT.run (m := Id) (OptionT.run f) env
  match out with
  | none => IO.println "Failure"
  | some a =>
      IO.println s!"output = {a}"
      IO.println s!"-------"
      IO.println s!"edges = {env.edges}"
      IO.println s!"comps = {env.comps.toList}"

def KargerM.run' (f : KargerM α) (env : KargerState) : Option (α × KargerState) :=
  let out : Option α × KargerState := StateT.run (m := Id) (OptionT.run f) env
  match out.1 with
  | none => none
  | some x => some ⟨x, out.2⟩

def runKarger (fuel := 1000) (env : KargerState) : Option Nat :=
  if fuel = 0 then failure
  else
    let cut := KargerM.run' getFinalComp env
    match cut with
    | none => none
    | some ⟨cut, state⟩ =>
        let n := countEdgesAcross cut state.edges
        dbg_trace s!"n = {n}"
        if n = 3 then
          return cut.size * (state.comps.size - cut.size)
        else
          runKarger (fuel-1) { env with rng := state.rng }

def printEdges (edges : Array (String × String)) : IO Unit := do
  for i in [0:edges.size] do
    IO.println s!"Edge {i}: {edges[i]!}"

def firstPart (input : FilePath) : IO String := do
  let some rawdevices := (← IO.FS.lines input).mapM (fun s => s.parse? parseDevice)
    | return "Parse error"
  let edges : Array (String × String) := rawdevices.foldl (init := #[]) fun acc node =>
    node.2.foldl (init := acc) fun acc' node' => acc'.push ⟨node.1, node'⟩
  let nodes : Std.HashMap String (Option String) :=
    edges.foldl (init := Std.HashMap.empty) fun mp edge =>
      (mp.insert edge.1 none).insert edge.2 none
  let initenv : KargerState :=
    { edges := edges
      comps := nodes
      rng := mkStdGen 2832 }
  let some out := runKarger 100 initenv | return "failure"
  return s!"{out}"

--#eval firstPart testinput1           --(ans: )
--#eval debug1 testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  return s!"I guess there's no part 2"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day25
