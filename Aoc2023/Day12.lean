import Aoc2023.Utils

open System Lean Lean.Parsec

/- # Advent of Code 2023 Day 12

## Problem statement

In the giant field just outside, the springs are arranged into rows. For each row, the condition
records show every spring and whether it is operational (.) or damaged (#). This is the part of the
condition records that is itself damaged; for some springs, it is simply unknown (?) whether the
spring is operational or damaged.

However, the engineer that produced the condition records also duplicated some of this information
in a different format! After the list of springs for a given row, the size of each contiguous group
of damaged springs is listed in the order those groups appear in the row. This list always accounts
for every damaged spring, and each number is the entire size of its contiguous group (that is,
groups are always separated by at least one operational spring: `####` would always be 4, never 2,2).

So, condition records with no unknown spring conditions might look like this:

#.#.### 1,1,3
.#...#....###. 1,1,3
.#.###.#.###### 1,3,1,6
####.#...#... 4,1,1
#....######..#####. 1,6,5
.###.##....# 3,2,1

However, the condition records are partially damaged; some of the springs' conditions are actually
unknown (?). For example:

???.### 1,1,3
.??..??...?##. 1,1,3
?#?#?#?#?#?#?#? 1,3,1,6
????.#...#... 4,1,1
????.######..#####. 1,6,5
?###???????? 3,2,1

Equipped with this information, it is your job to figure out how many different arrangements of
operational and broken springs fit the given criteria in each row.
-/

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

/-- Can we place a block of size `sz` with the last `#` at position `pos`? This includes checking
that the character before the block is `.` -/
def canPlace (sz : Nat) (pos : Nat) (spr : Array Char) : Bool :=
  if sz > pos then false
  else
    (canBeDot spr[pos-sz]!)
      ∧ spr.foldl (init := true) (start := pos + 1 - sz) (stop := pos+1)
            fun acc c => acc && canBeHash c

/-- Dynamic programming solution, based on the 2D array `vals[i][j]` which is supposed to contain
 the number of possible ways of arranging the first `j` blocks up to position `i` (where 0 really
 means no blocks at all, not the first block, hence the `k+1` below). Note that we added
 an extra `.` at the beginning to avoid out-of-bound errors when calling `canPlace`.

  The idea is that there are two kinds of arrangements: those for which the last block finishes
  exactly at position `j`, and those for which it doesn't. For the first kind, we can check if
  it's possible to place the last block at the end, i.e. we can have the right number of `#`,
  plus a `.` just before, and if we can then it's just equal to the number of arrangements of the first
  `j-1` blocks in the first `i - sz - 1` positions where `sz` is the size of the current block.
  (Otherwise it's just 0.)

  For the second kind, we have to check that the current position can be a `.`. If so, then it's
  the number of arrangements of the first `j` blocks in the first `i-1` positions, otherwise it's
  0.

  We then systematically fill up this array starting at 0,0 and work our way up to the full problem.
 -/
def countArrangements (spr : Array Char) (nums : Array Nat) : Nat := Id.run do
  let n := spr.size
  let k := nums.size
  let mut vals := Array.mkArray₂ n (k+1) 0

  /- Initialize the first row (i.e. no blocks at all). There's only one arrangement
    until we hit the first `#`, after which it's zero. -/
  for i in [0:n] do
    if spr[i]! == '#' then break
    vals := vals.set₂ i 0 1

  /- Main loop where we fill up the array using the recurrence relation: -/
  for hi : i in [1:n] do
    for j in [1:(k+1)] do
      let curSize := nums[j-1]!
      /- `vhash` is the number of arrangements of the first kind: -/
      let vhash := if canPlace curSize i spr then vals.get₂! (i - curSize - 1) (j-1) else 0
      /- `vdot` is the number of arrangements of the second kind: -/
      let vdot := if canBeDot spr[i] then vals.get₂! (i-1) j else 0
      /- Hence the total is the sum of the two kinds: -/
      vals := vals.set₂ i j (vhash + vdot)

  /- Return the solution to the full problem, i.e. place all the blocks up to position `n-1`: -/
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

--#eval secondPart testinput1           --(ans: 525152)
--#eval secondPart realinput           --(ans: 3476169006222)

end Day12
