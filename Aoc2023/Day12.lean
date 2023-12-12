import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day12

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_12_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_12_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_12"

/-
PART 1:
-/

def parseLine : Parsec (Array Char × Array Nat) := do
  let springs ← many (pchar '?' <|> pchar '.' <|> pchar '#')
  ws
  let groups ← sepByA natNum (pchar ',')
  return ⟨springs, groups⟩

def canBeDot : Char → Bool
| '.' => true | '?' => true | _ => false

def canBeHash : Char → Bool
| '#' => true | '?' => true | _ => false

def canPlace (sz : Nat) (pos : Nat) (spr : Array Char) : Bool :=
  if sz > pos then false
  else
    (canBeDot spr[pos-sz]!)
      ∧ spr.foldl (init := true) (start := pos + 1 - sz) (stop := pos+1)
            fun acc c => acc && canBeHash c

def countArrangements (spr : Array Char) (nums : Array Nat) : Nat := Id.run do
  let n := spr.size
  let k := nums.size
  let mut vals := Array.mkArray₂ n (k+1) 0
  vals := vals.set₂ 0 0 1
  for i in [0:n] do
    if spr[i]! == '#' then break
    vals := vals.set₂ i 0 1
  for i in [1:n] do
    for j in [1:(k+1)] do
      let newval :=
        match spr[i]! with
        | '.' => vals.get₂! (i-1) j
        | '#' =>
          let curSize := nums[j-1]!
          if canPlace curSize i spr then
            vals.get₂! (i-nums[j-1]! - 1) (j-1)
          else 0
        | '?' =>
          let curSize := nums[j-1]!
          let vdot := vals.get₂! (i-1) j
          let vhash :=
            if canPlace curSize i spr then
              vals.get₂! (i- curSize - 1) (j-1)
            else 0
          vdot + vhash
        | _ => panic!"weird character found"
      vals := vals.set₂ i j newval
  --dbg_trace s!"{vals}"
  return vals[n-1]![k]!

def firstPart (input : FilePath) : IO String := do
  let some lines := (← IO.FS.lines input).mapM fun line => line.parse? parseLine
    | return "Parse error"
  let lines : Array (Array Char × Array Nat) := lines.map fun line => ⟨#['.'] ++ line.1, line.2⟩
  let out : Array Nat := lines.map fun line => countArrangements line.1 line.2
  return s!"{out.sum}"

--#eval firstPart testinput1           --(ans: 21)
--#eval debug1 5 testinput1           --(ans: 21)
--#eval firstPart realinput           --(ans: 7007)

/-
PART 2:
-/

def blowSprings (rs : Array Char) : Array Char := Id.run do
  let mut out := #[]
  for _ in [0:4] do
    out := (out ++ rs).push '?'
  return out ++ rs

def blowRecord (rs : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  for _ in [0:5] do
    out := out ++ rs
  return out

def secondPart (input : FilePath) : IO String := do
  let some lines := (← IO.FS.lines input).mapM fun line => line.parse? parseLine
    | return "Parse error"
  let lines : Array (Array Char × Array Nat):= lines.map fun line => ⟨(blowSprings line.1).push '.', blowRecord line.2⟩
  let lines : Array (Array Char × Array Nat) := lines.map fun line => ⟨#['.'] ++ line.1, line.2⟩
  let out : Array Nat := lines.map fun line => countArrangements line.1 line.2
  return s!"{out.sum}"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day12
