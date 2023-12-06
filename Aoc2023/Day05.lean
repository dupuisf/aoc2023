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

abbrev Map := Array MapEntry

def parseSeeds : Parsec (List Int) := pstring "seeds: " *> sepBy natNum whites

def parseMapEntry : Parsec MapEntry := do
  let destStart ← natNum
  ws
  let srcStart ← natNum
  ws
  let len ← natNum
  return ⟨destStart, srcStart, len⟩

def parseMap : Parsec Map := do
  let _ ← manyChars asciiLetter
  let _ ← pstring "-to-"
  let _ ← manyChars asciiLetter
  let _ ← pstring " map:\n"
  let entries ← sepBy parseMapEntry newlineChar
  return ⟨entries⟩

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
  for e in m do
    let some z := e.apply x | continue
    return z
  return x

def applyMaps (ms : List Map) (x : Int) : Int :=
  ms.foldl (init := x) fun z m => m.apply z

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

def _root_.Array.last (as : Array α) : Option α := as[as.size-1]?

def _root_.Array.maybePush (as : Array α) (a? : Option α) : Array α :=
  match a? with
  | none => as
  | some x => as.push x

def _root_.Array.keep? (as : Array α) (keep : α → α → α) : Option α :=
  as.foldl (init := none) fun acc x => match acc with
                                       | none => some x
                                       | some z => some (keep z x)

def parseSeedRanges : Parsec (List (Int × Int)) :=
  let numPair : Parsec (Int × Int) := do let n₁ ← natNum; ws; let n₂ ← natNum; return ⟨n₁, n₂⟩
  pstring "seeds: " *> sepBy numPair whites

def parseInput₂ : Parsec (List (Int × Int) × List Map) := do
  let sRanges ← parseSeedRanges
  let _ ← many newlineChar
  let maps ← parseMaps
  return ⟨sRanges, maps⟩

def rangeIntersect (r₁ r₂ : Int × Int) : Option (Int × Int) := Id.run do
  let r₁_end := r₁.1 + r₁.2 - 1
  let r₂_end := r₂.1 + r₂.2 - 1
  if r₁.1 > r₂_end then return none
  if r₂.1 > r₁_end then return none
  let start := max r₁.1 r₂.1
  let len := min r₁_end r₂_end - start + 1
  return some ⟨start, len⟩

def MapEntry.mapRange (e : MapEntry) (r : Int × Int) : Option (Int × Int) := Id.run do
  let some ⟨st, len⟩ := rangeIntersect ⟨e.srcStart, e.len⟩ ⟨r.1, r.2⟩ | return none
  let offset := e.destStart - e.srcStart
  return some ⟨st + offset, len⟩

def Map.toNF (m : Map) : Map := Id.run do
  let sorted : Array MapEntry := m.qsort (fun x y => x.srcStart ≤ y.srcStart)
  let mut out : Array MapEntry := #[]
  let mut curPos := 0
  for e in sorted do
    if e.srcStart > curPos then out := out.push ⟨curPos, curPos, e.srcStart - curPos⟩
    out := out.push e
    curPos := e.srcStart + e.len
  return out

-- Assumes NF
def Map.mapRange (m : Map) (r : Int × Int) : Array (Int × Int) := Id.run do
  let preoutput := m.foldl (init := #[]) fun acc e => acc.maybePush (e.mapRange r)
  let some lastElem := m.last | panic! "Oh no"
  let lastEntry : MapEntry :=
    ⟨lastElem.srcStart + lastElem.len, lastElem.srcStart + lastElem.len, r.1 + r.2 + 1⟩
  preoutput.maybePush (lastEntry.mapRange r)

def allMaps (ms : List Map) (ranges : Array (Int × Int)) : Array (Int × Int) :=
  match ms with
  | .nil => ranges
  | .cons m rest =>
      let newranges := ranges.concatMap m.mapRange
      allMaps rest newranges

def secondPart (input : FilePath) : IO Int := do
  let rawdata := (← IO.FS.readFile input)
  let some ⟨ranges, ms⟩ := rawdata.parse? parseInput₂ | panic! "parse error"
  let msNF := ms.map Map.toNF
  let maps := msNF
  --let maps := msNF.take 7
  let finalRanges := allMaps maps ranges.toArray
  IO.println <| ms.get! 2
  IO.println finalRanges
  let some z := finalRanges.keep? fun x y => if x.1 < y.1 then x else y | panic! "Oh no"
  return z.1

--#eval secondPart testinput   --(ans: 46)
--#eval secondPart realinput   --(ans: 99751240)

end Day05
