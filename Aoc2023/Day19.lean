import Aoc2023.Utils
import Std.Data.HashMap.Basic

open System Lean Lean.Parsec

namespace Day19

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_19_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_19_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_19"

/-
PART 1:
-/

structure Part where
  x : Nat
  m : Nat
  a : Nat
  s : Nat
deriving BEq, Inhabited, Repr

instance : ToString Part where
  toString x := s!"⟨{x.x}, {x.m}, {x.a}, {x.s}⟩"

structure Rule where
  attr : Char
  lt : Bool
  thresh : Nat
  dest : String
deriving Inhabited

instance : ToString Rule where
  toString r := match r.lt with
                | true => s!"{r.attr}<{r.thresh}:{r.dest}"
                | false => s!"{r.attr}>{r.thresh}:{r.dest}"

def Rule.negate (r : Rule) : Rule :=
  if r.lt then
    { r with lt := false, thresh := r.thresh-1 }
  else
    { r with lt := true, thresh := r.thresh+1 }

def Rule.test (r : Rule) (pr : Part) : Bool :=
  match r.attr, r.lt with
  | 'x', false => (pr.x > r.thresh)
  | 'm', false => (pr.m > r.thresh)
  | 'a', false => (pr.a > r.thresh)
  | 's', false => (pr.s > r.thresh)
  | 'x', true => (pr.x < r.thresh)
  | 'm', true => (pr.m < r.thresh)
  | 'a', true => (pr.a < r.thresh)
  | 's', true => (pr.s < r.thresh)
  | _, _ => true

structure Workflow where
  name : String
  rules : List Rule
deriving Inhabited

def parseRule : Parsec Rule := attempt do
  let attr ← anyChar
  let op ← (pchar '<' <|> pchar '>')
  let num ← natNum
  let _ ← pchar ':'
  let dest ← word
  match op with
  | '>' => return ⟨attr, false, num, dest⟩
  | '<' => return ⟨attr, true, num, dest⟩
  | _ => panic! "oh no"

def parseTrivialRule : Parsec Rule := attempt do
  let dest ← word
  return ⟨'!', true, 0, dest⟩

def parseWorkflow : Parsec (String × List Rule) := do
  let name ← word
  let _ ← pchar '{'
  let rules ← sepBy (parseRule <|> parseTrivialRule) (pchar ',')
  let _ ← pchar '}'
  return ⟨name, rules⟩

def parseWorkflows : Parsec (Std.HashMap String (List Rule)) := do
  let flows ← sepBy parseWorkflow newlineChar
  return Std.HashMap.ofList flows

def parsePart : Parsec Part := do
  let _ ← pstring "{x="
  let x ← natNum
  let _ ← pstring ",m="
  let m ← natNum
  let _ ← pstring ",a="
  let a ← natNum
  let _ ← pstring ",s="
  let s ← natNum
  let _ ← pchar '}'
  return ⟨x,m,a,s⟩

def parseFile : Parsec ((Std.HashMap String (List Rule)) × List Part) := do
  let flows ← parseWorkflows
  let _ ← many1 newlineChar
  let parts ← sepBy parsePart newlineChar
  return ⟨flows, parts⟩

def applyFlow (pr : Part) (flow : List Rule) : String := Id.run do
  for r in flow do
    if r.test pr then return r.dest
  panic! "oh no"

partial def processPart (pr : Part) (flows : Std.HashMap String (List Rule))
    (rulename : String) : Bool :=
  match flows.find? rulename with
  | none => panic! "ho no"
  | some flow =>
      let dest := applyFlow pr flow
      match dest with
      | "A" => true
      | "R" => false
      | name => processPart pr flows name

def debug1 (input : FilePath) : IO String := do
  let some ⟨flows, parts⟩ := (← IO.FS.readFile input).parse? parseFile
      | return "Parse error"
  let out : Nat := parts.foldl (init := 0) fun acc part =>
    if processPart part flows "in" then
      acc + part.x + part.m + part.a + part.s
    else
      acc
  return s!"{out}"

def firstPart (input : FilePath) : IO String := do
  let some ⟨flows, parts⟩ := (← IO.FS.readFile input).parse? parseFile
      | return "Parse error"
  let out : Nat := parts.foldl (init := 0) fun acc part =>
    if processPart part flows "in" then
      acc + part.x + part.m + part.a + part.s
    else
      acc
  return s!"{out}"

--#eval firstPart testinput1           --(ans: 19114)
--#eval debug1 testinput1           --(ans: )
--#eval firstPart realinput           --(ans: 352052)

/-
PART 2:
-/

structure State where
  xlb : Nat
  xub : Nat
  mlb : Nat
  mub : Nat
  alb : Nat
  aub : Nat
  slb : Nat
  sub : Nat
deriving BEq, Repr

def State.count (s : State) :=
  let x := if s.xub < s.xlb then 0 else s.xub - s.xlb + 1
  let m := if s.mub < s.mlb then 0 else s.mub - s.mlb + 1
  let a := if s.aub < s.alb then 0 else s.aub - s.alb + 1
  let s := if s.sub < s.slb then 0 else s.sub - s.slb + 1
  x * m * a * s

def State.applyRule (s : State) (r : Rule) : State :=
  match r.attr, r.lt with
  | 'x', false => { s with xlb := max s.xlb (r.thresh+1) }
  | 'm', false => { s with mlb := max s.mlb (r.thresh+1) }
  | 'a', false => { s with alb := max s.alb (r.thresh+1) }
  | 's', false => { s with slb := max s.slb (r.thresh+1) }
  | 'x', true => { s with xub := min s.xub (r.thresh-1) }
  | 'm', true => { s with mub := min s.mub (r.thresh-1) }
  | 'a', true => { s with aub := min s.aub (r.thresh-1) }
  | 's', true => { s with sub := min s.sub (r.thresh-1) }
  | _, _ => s

partial def search (flows : Std.HashMap String (List Rule))
    (state : State) (seen : Std.HashMap String Bool)
    (cur : String) : Nat := Id.run do
  match cur with
  | "A" => return state.count
  | "R" => return 0
  | _ =>
    let some visited := seen.find? cur | panic! s!"key not found: {cur}"
    if visited ∨ (state.count = 0) then return 0
    let some rules := flows.find? cur | panic! s!"key not found: {cur}"
    let mut out := 0
    let mut curstate := state
    for r in rules do
      let tmpstate := curstate.applyRule r
      let newseen := seen.modify cur (fun _ _ => true)
      out := out + search flows tmpstate newseen r.dest
      curstate := curstate.applyRule r.negate
    return out

def secondPart (input : FilePath) : IO String := do
  let some ⟨flows, _⟩ := (← IO.FS.readFile input).parse? parseFile
      | return "Parse error"
  let flowNames : List String := flows.fold (fun ks k _ => k :: ks) []
  let initSeen : Std.HashMap String Bool := Std.HashMap.ofList <|
    flowNames.foldl (init := []) fun acc nm => ⟨nm, false⟩ :: acc
  let initState : State := ⟨1, 4000, 1, 4000, 1, 4000, 1, 4000⟩
  let out := search flows initState initSeen "in"
  return s!"{out}"

--#eval secondPart testinput1           --(ans: 167409079868000)
--#eval secondPart realinput           --(ans: 116606738659695)

end Day19
