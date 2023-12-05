import Aoc2023.Utils

open System Lean Lean.Parsec

namespace Day05

def testinput : FilePath := "/home/fred/lean/aoc2023/input_05_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_05_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_05"

/-
PART 1:
-/

/- # Parser -/

structure MapEntry where
  destStart : Int
  srcStart : Int
  len : Int
deriving Inhabited, Repr

instance : ToString MapEntry where
  toString x := s!"dest = {x.destStart}, src = {x.srcStart}, len = {x.len}"

structure Map where
  srcType : String
  destType : String
  entries : List MapEntry
deriving Inhabited, Repr

def parseSeeds : Parsec (List Int) := pstring "seeds: " *> sepBy natNum whites

def parseMapEntry : Parsec MapEntry := do
  let destStart ← natNum
  ws
  let srcStart ← natNum
  ws
  let len ← natNum
  return ⟨destStart, srcStart, len⟩

def parseMap : Parsec Map := do
  let src ← manyChars asciiLetter
  let _ ← pstring "-to-"
  let dest ← manyChars asciiLetter
  let _ ← pstring " map:\n"
  let entries ← sepBy parseMapEntry newlineChar
  return ⟨src, dest, entries⟩

def parseMaps : Parsec (List Map) := sepBy parseMap (many newlineChar)

def parseInput : Parsec (List Int × List Map) := do
  let seeds ← parseSeeds
  let _ ← many newlineChar
  let maps ← parseMaps
  return ⟨seeds, maps⟩

/- # Mapping logic -/

/-- If output is `some z`, then the entry maps `x` to `z`, otherwise `x`
was out of range. -/
def MapEntry.apply (e : MapEntry) (x : Int) : Option Int :=
  if x ≥ e.srcStart ∧ x < e.srcStart + e.len then some (x + (e.destStart - e.srcStart))
  else none

def Map.apply (m : Map) (x : Int) : Int := Id.run do
  for e in m.entries do
    let some z := e.apply x | continue
    return z
  return x

def applyMaps (ms : List Map) (x : Int) : Int :=
  ms.foldl (init := x) fun z m => m.apply z

--def testMap := "seed-to-soil map:
--50 98 2
--52 50 48".yoloParse parseMap
--
--#eval testMap.apply 99

def _root_.List.min [LE α] [DecidableRel (α := α) (· ≤ ·)] (as : List α) : Option α :=
  match as with
  | [] => none
  | x :: _ =>
    let out : α := as.foldl (init := x) fun min z => if z ≤ min then z else min
    some out

def firstPart (input : FilePath) : IO Int := do
  let rawdata := (← IO.FS.readFile input)
  let some ⟨seeds, ms⟩ := rawdata.parse? parseInput | panic! "parse error"
  let dests := seeds.map (applyMaps ms ·)
  let some out := dests.min | panic! "no numbers"
  return out

--#eval firstPart testinput   --(ans: 35)
--#eval firstPart realinput   --(ans: 51580674)

/-
PART 2:
-/

def parseSeedRanges : Parsec (List (Int × Int)) :=
  let numPair : Parsec (Int × Int) := do let n₁ ← natNum; ws; let n₂ ← natNum; return ⟨n₁, n₂⟩
  pstring "seeds: " *> sepBy numPair whites

def parseInput₂ : Parsec (List (Int × Int) × List Map) := do
  let sRanges ← parseSeedRanges
  let _ ← many newlineChar
  let maps ← parseMaps
  return ⟨sRanges, maps⟩

#eval "seeds: 79 14 55 13".parse? parseSeedRanges

def secondPart (input : FilePath) : IO Int := do
  let rawdata := (← IO.FS.lines input)
  return 0

--#eval secondPart testinput
--#eval secondPart realinput

end Day05
