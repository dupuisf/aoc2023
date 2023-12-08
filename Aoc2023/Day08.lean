import Aoc2023.Utils
import Std.Data.BitVec.Basic
import Std.Data.Nat.Gcd

open System Lean Lean.Parsec

namespace Day08

def testinput : FilePath := "/home/fred/lean/aoc2023/input_08_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_08_test2"
def testinput3 : FilePath := "/home/fred/lean/aoc2023/input_08_test3"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_08"

/-
PART 1:
-/

def parseNode : Parsec (String × String × String) := do
  let name ← manyChars alphanum
  let _ ← pstring " = ("
  let left ← manyChars alphanum
  let _ ← pstring ", "
  let right ← manyChars alphanum
  let _ ← pstring ")"
  return ⟨name, left, right⟩

def parseInput : Parsec (String × Array (String × String × String)) := do
  let instructions ← manyChars (pchar 'R' <|> pchar 'L')
  let _ ← newlineChar
  let _ ← newlineChar
  let nodes ← sepByA parseNode newlineChar
  return ⟨instructions, nodes⟩

def convertNodes? (nodes : Array (String × String × String)) : Option (Array (Nat × Nat)) :=
  nodes.foldl (init := some #[]) fun acc node => Id.run do
    let some acc := acc | return none
    let some idxleft := nodes.binSearchIdx ⟨node.2.1, ⟨"", ""⟩⟩ (fun n1 n2 => n1.1 < n2.1) | return none
    let some idxright := nodes.binSearchIdx ⟨node.2.2, ⟨"", ""⟩⟩ (fun n1 n2 => n1.1 < n2.1) | return none
    some <| acc.push ⟨idxleft, idxright⟩

partial def run (nodes : Array (Nat × Nat)) (instructions : Array Bool) (curinst := 0) (curnode := 0) (clock := 0): Nat :=
  if curnode = nodes.size - 1 then clock
  else
    if instructions[curinst]! then
      -- move right
      run nodes instructions ((curinst + 1) % instructions.size) (nodes[curnode]!.2) (clock + 1)
    else
      -- move left
      run nodes instructions ((curinst + 1) % instructions.size) (nodes[curnode]!.1) (clock + 1)

def firstPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.readFile input)
  let some ⟨rawinstructions, rawnodes⟩ := rawdata.parse? parseInput | panic! "No instructions"
  let sortednodes := rawnodes.qsort (fun x y => x.1 < y.1)
  let some nodes := convertNodes? sortednodes | panic! "Failed to convert nodes"
  let instructions := rawinstructions.foldl (init := #[])
    fun acc c => match c with
                 | 'R' => acc.push true
                 | 'L' => acc.push false
                 | _ => panic! "Oh no"
  return run nodes instructions

--#eval firstPart testinput           --(ans: 2)
--#eval firstPart testinput2           --(ans: 6)
--#eval firstPart realinput           --(ans: 18113)

/-
PART 2:
-/

partial def run₂ (nodes : Array (Nat × Nat)) (instructions : Array Bool) (stop : Array Nat)
    (curnode : Nat) (curinst := 0) (clock := 0) : Nat :=
  if stop.contains curnode then clock
  else
    if instructions[curinst]! then
      -- move right
      run₂ nodes instructions stop (nodes[curnode]!.2) ((curinst + 1) % instructions.size) (clock + 1)
    else
      -- move left
      run₂ nodes instructions stop (nodes[curnode]!.1) ((curinst + 1) % instructions.size) (clock + 1)


def secondPart (input : FilePath) : IO Nat := do
  let rawdata := (← IO.FS.readFile input)
  let some ⟨rawinstructions, rawnodes⟩ := rawdata.parse? parseInput | panic! "No instructions"
  let sortednodes := rawnodes.qsort (fun x y => x.1 < y.1)
  let some nodes := convertNodes? sortednodes | panic! "Failed to convert nodes"
  let instructions := rawinstructions.foldl (init := #[])
    fun acc c => match c with
                 | 'R' => acc.push true
                 | 'L' => acc.push false
                 | _ => panic! "Oh no"
  let start := sortednodes.getAllIdx fun node => node.1.toCharArray[2]! = 'A'
  let stop := sortednodes.getAllIdx fun node => node.1.toCharArray[2]! = 'Z'
  let times := start.map fun node => run₂ nodes instructions stop node
  return times.foldl (init := 1) Nat.lcm


--#eval secondPart testinput3           --(ans: 6)
--#eval secondPart realinput           --(ans: 12315788159977)

end Day08
