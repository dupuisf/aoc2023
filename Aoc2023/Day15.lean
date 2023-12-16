import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day15

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_15_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_15_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_15"

/-
PART 1:
-/

def getHash (str : String) : Fin 256 :=
  let num := str.foldl (init := 0) fun acc c => ((acc + c.toNat) * 17)
  have : num % 256 < 256 := Nat.mod_lt _ <| Nat.zero_lt_succ _
  ⟨num % 256, this⟩

def firstPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.readFile input).trim.splitOn ","
  let hashed := rawdata.map getHash
  let sum : Nat := hashed.foldl (init := (0:Nat)) (fun x (y : Fin 256) => (x : Nat) + (y : Nat))
  return s!"{sum}"

--#eval firstPart testinput1           --(ans: 1320)
--#eval firstPart realinput           --(ans: 505427)

/-
PART 2:
-/

inductive Operation
| dash (label : String) (hash : Fin 256)
| equals (label : String) (hash : Fin 256) (len : Nat)
deriving BEq, Repr

instance : ToString Operation where
  toString x := match x with
                | .dash label hash => s!"{label}({hash})-"
                | .equals label hash len => s!"{label}({hash}) = {len}"

def parseOperation : Parsec Operation := do
  let label := String.ofCharArray <| ← many1 alphanum
  let hash := getHash label
  let opchar ← anyCharThat (fun c => c == '=' || c == '-')
  if opchar == '=' then
    let num ← natNum
    return .equals label hash num
  else
    return .dash label hash

def parseInput : Parsec (List Operation) :=
  sepBy parseOperation (pchar ',')

def execInstr (instr : Operation) (boxes : Vec 256 (List (String × Nat))) :
    Vec 256 (List (String × Nat)) :=
    match instr with
    | .dash label hash =>
        let newcontent := boxes[hash].eraseP (·.1 == label)
        boxes.set hash newcontent
    | .equals label hash len =>
        match boxes[hash].findIdx? (fun box => box.1 == label) with
        | none =>
            let newcontent := boxes[hash] ++ [⟨label, len⟩]
            boxes.set hash newcontent
        | some idx =>
            let newcontent := boxes[hash].set idx ⟨label, len⟩
            boxes.set hash newcontent

def execInstrList (instrList : List Operation) (boxes : Vec 256 (List (String × Nat))) :
    Vec 256 (List (String × Nat)) :=
  match instrList with
  | [] => boxes
  | x :: xs => execInstrList xs (execInstr x boxes)

def getPower (boxes : Vec 256 (List (String × Nat))) : Nat := Id.run do
  let mut out := 0
  for hi : i in [0:256] do
    out := out + (i + 1) * boxes[i].foldlIdx (init := 0) fun idx acc x => acc + (idx+1) * x.2
  pure out

def printBoxes (boxes : Vec 256 (List (String × Nat))) : IO Unit := do
  for hi : i in [0:256] do
    if boxes[i] != [] then
      IO.println s!"Box {i} : {boxes[i]}"

def debug2 : IO String := do
  let some inp := "rn=1,cm-,qp=3,cm=2".parse? parseInput | return "Parse error"
  let boxes : Vec 256 (List (String × Nat)) := Vec.mkVec 256 []
  let boxes' := execInstrList inp boxes
  printBoxes boxes'
  return s!"bla"

def secondPart (input : FilePath) : IO String := do
  let some inp := (← IO.FS.readFile input).trim.parse? parseInput | return "Parse error"
  let boxes : Vec 256 (List (String × Nat)) := Vec.mkVec 256 []
  let boxes' := execInstrList inp boxes
  return s!"{getPower boxes'}"

--#eval secondPart testinput1           --(ans: 145)
--#eval debug2    --(ans: )
--#eval secondPart realinput           --(ans: 243747)

end Day15
