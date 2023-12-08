import Aoc2023.Utils
import Std.Data.Fin.Lemmas

open System Lean Lean.Parsec

namespace Day07

def testinput : FilePath := "/home/fred/lean/aoc2023/input_07_test"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_07_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_07"

/-
PART 1:
-/

/- # Data types -/

def Card := Fin 13
deriving Inhabited, BEq

instance Card.coeToNat : CoeOut Card Nat := Fin.coeToNat

def Hand := {as : Array Card // as.size = 5}

instance : OfNat Card 0 := ⟨(0 : Fin 13)⟩
instance : OfNat Card 1 := ⟨(1 : Fin 13)⟩
instance : OfNat Card 2 := ⟨(2 : Fin 13)⟩
instance : OfNat Card 3 := ⟨(3 : Fin 13)⟩
instance : OfNat Card 4 := ⟨(4 : Fin 13)⟩
instance : OfNat Card 5 := ⟨(5 : Fin 13)⟩
instance : OfNat Card 6 := ⟨(6 : Fin 13)⟩
instance : OfNat Card 7 := ⟨(7 : Fin 13)⟩
instance : OfNat Card 8 := ⟨(8 : Fin 13)⟩
instance : OfNat Card 9 := ⟨(9 : Fin 13)⟩
instance : OfNat Card 10 := ⟨(10 : Fin 13)⟩
instance : OfNat Card 11 := ⟨(11 : Fin 13)⟩
instance : OfNat Card 12 := ⟨(12 : Fin 13)⟩

def Card.toChar : Card → Char
| 0 => '2' | 1 => '3' | 2 => '4' | 3 => '5' | 4 => '6' | 5 => '7'
| 6 => '8' | 7 => '9' | 8 => 'T' | 9 => 'J' | 10 => 'Q' | 11 => 'K'
| 12 => 'A' | _ => 'E'

instance : ToString Card where
  toString c :=
    match c.val with
      | 0 => "2" | 1 => "3" | 2 => "4" | 3 => "5" | 4 => "6" | 5 => "7"
      | 6 => "8" | 7 => "9" | 8 => "T" | 9 => "J" | 10 => "Q" | 11 => "K"
      | 12 => "A" | _ => "error"

instance : ToString Hand where
  toString hand := hand.val.foldl (init := "") fun str i => str.push i.toChar

instance : Inhabited Hand where
  default := ⟨#[0,0,0,0,0], by simp⟩

def charToCard : Char → Option Card
| '2' => some 0
| '3' => some 1
| '4' => some 2
| '5' => some 3
| '6' => some 4
| '7' => some 5
| '8' => some 6
| '9' => some 7
| 'T' => some 8
| 'J' => some 9
| 'Q' => some 10
| 'K' => some 11
| 'A' => some 12
| _   => none

instance : LT Card where
  lt x y := x.val < y.val

instance : DecidableRel (α := Card) (· < ·) :=
  inferInstanceAs (DecidableRel (α := Card) (·.val < ·.val))

def Hand.stats (hand : Hand) : {as : Array Nat // as.size = 13} :=
  hand.val.foldl (init := ⟨mkArray 13 0, by simp⟩)
    fun acc c =>
      have : c.val < acc.val.size := by
        calc (c : Nat) < 13  := by simp
                    _ = acc.val.size := acc.property.symm
      let out := acc.val.natSet c.val (acc[c.val] + 1)
      ⟨out, by simp only [out, Array.size_natSet, acc.property]⟩

def Hand.ltRule2 (hnd₁ hnd₂ : Hand) : Bool :=
  go hnd₁.val.data hnd₂.val.data where
  go l₁ l₂ := match l₁, l₂ with
              | [], [] => false
              | (c₁ :: r₁), (c₂ :: r₂) =>
                if c₁ < c₂ then true
                else if c₁ > c₂ then false
                else go r₁ r₂
              | _, _ => false

def Hand.type (hand : Hand) : Nat :=
  let st := hand.stats
  if st.val.contains 5 then 6
  else if st.val.contains 4 then 5
  else if (st.val.contains 3) ∧ (st.val.contains 2) then 4
  else if (st.val.contains 3) ∧ ¬(st.val.contains 2) then 3
  else if (st.val.count (· = 2)) = 2 then 2
  else if ((st.val.count (· = 2)) = 1) ∧ ¬(st.val.contains 3) then 1
  else 0

def Hand.lt (x y : Hand) : Bool :=
  if x.type < y.type then true
  else if y.type < x.type then false
  else Hand.ltRule2 x y

/- # Parsing -/

@[inline]
def parseCard : Parsec Card := attempt do
  let c ← anyChar
  if ('2' ≤ c ∧ c ≤ '9') then
    let some x := charToCard c | fail "Oh no!"
    return x
  match c with
  | 'T' => return 8
  | 'J' => return 9
  | 'Q' => return 10
  | 'K' => return 11
  | 'A' => return 12
  | _ => fail "Card expected"

def parseHand : Parsec Hand := attempt do
  let c₁ ← parseCard
  let c₂ ← parseCard
  let c₃ ← parseCard
  let c₄ ← parseCard
  let c₅ ← parseCard
  return ⟨#[c₁, c₂, c₃, c₄, c₅], by simp⟩

def parseBid : Parsec (Hand × Nat) := do
  let hand ← parseHand
  ws
  let bid ← natNum
  return ⟨hand, bid⟩

def firstPart (input : FilePath) : IO Nat := do
  let bids : Array (Hand × Nat) := (← IO.FS.lines input).foldl (init := #[])
    fun acc str => acc.push (str.yoloParse parseBid)
  let sorted : Array (Hand × Nat) := bids.qsort (Hand.lt ·.1 ·.1)
  return sorted.foldlIdx (init := 0)
    fun idx acc bid => acc + (idx + 1) * bid.2

--#eval firstPart testinput     --(ans: 6440)
--#eval firstPart realinput     --(ans: 251106089)

end Day07

/- ************************************************************************ -/

namespace Day07part2

/- # Data types -/

def Card := Fin 13
deriving Inhabited, BEq

instance Card.coeToNat : CoeOut Card Nat := Fin.coeToNat

def Hand := {as : Array Card // as.size = 5}

instance : OfNat Card 0 := ⟨(0 : Fin 13)⟩
instance : OfNat Card 1 := ⟨(1 : Fin 13)⟩
instance : OfNat Card 2 := ⟨(2 : Fin 13)⟩
instance : OfNat Card 3 := ⟨(3 : Fin 13)⟩
instance : OfNat Card 4 := ⟨(4 : Fin 13)⟩
instance : OfNat Card 5 := ⟨(5 : Fin 13)⟩
instance : OfNat Card 6 := ⟨(6 : Fin 13)⟩
instance : OfNat Card 7 := ⟨(7 : Fin 13)⟩
instance : OfNat Card 8 := ⟨(8 : Fin 13)⟩
instance : OfNat Card 9 := ⟨(9 : Fin 13)⟩
instance : OfNat Card 10 := ⟨(10 : Fin 13)⟩
instance : OfNat Card 11 := ⟨(11 : Fin 13)⟩
instance : OfNat Card 12 := ⟨(12 : Fin 13)⟩

def Card.toChar : Card → Char
| 0 => 'J' | 1 => '2' | 2 => '3' | 3 => '4' | 4 => '5' | 5 => '6'
| 6 => '7' | 7 => '8' | 8 => '9' | 9 => 'T' | 10 => 'Q' | 11 => 'K'
| 12 => 'A' | _ => 'E'

instance : ToString Card where
  toString c :=
    match c.val with
    | 0 => "J" | 1 => "2" | 2 => "3" | 3 => "4" | 4 => "5" | 5 => "6"
    | 6 => "7" | 7 => "8" | 8 => "9" | 9 => "T" | 10 => "Q" | 11 => "K"
    | 12 => "A" | _ => "E"

instance : ToString Hand where
  toString hand := hand.val.foldl (init := "") fun str i => str.push i.toChar

instance : Inhabited Hand where
  default := ⟨#[0,0,0,0,0], by simp⟩

def charToCard : Char → Option Card
| 'J' => some 0
| '2' => some 1
| '3' => some 2
| '4' => some 3
| '5' => some 4
| '6' => some 5
| '7' => some 6
| '8' => some 7
| '9' => some 8
| 'T' => some 9
| 'Q' => some 10
| 'K' => some 11
| 'A' => some 12
| _   => none

instance : LT Card where
  lt x y := x.val < y.val

instance : DecidableRel (α := Card) (· < ·) :=
  inferInstanceAs (DecidableRel (α := Card) (·.val < ·.val))

def Hand.stats (hand : Hand) : {as : Array Nat // as.size = 13} :=
  hand.val.foldl (init := ⟨mkArray 13 0, by simp⟩)
    fun acc c =>
      have : c.val < acc.val.size := by
        calc (c : Nat) < 13  := by simp
                    _ = acc.val.size := acc.property.symm
      let out := acc.val.natSet c.val (acc[c.val] + 1)
      ⟨out, by simp only [out, Array.size_natSet, acc.property]⟩

def Hand.ltRule2 (hnd₁ hnd₂ : Hand) : Bool :=
  go hnd₁.val.data hnd₂.val.data where
  go l₁ l₂ := match l₁, l₂ with
              | [], [] => false
              | (c₁ :: r₁), (c₂ :: r₂) =>
                if c₁ < c₂ then true
                else if c₁ > c₂ then false
                else go r₁ r₂
              | _, _ => false

def Hand.type (hand : Hand) : Nat :=
  let st := hand.stats
  let jokers := st[0]
  match jokers with
  | 0 =>
    if st.val.contains 5 then 6
    else if st.val.contains 4 then 5
    else if (st.val.contains 3) ∧ (st.val.contains 2) then 4
    else if (st.val.contains 3) ∧ ¬(st.val.contains 2) then 3
    else if (st.val.count (· = 2)) = 2 then 2
    else if ((st.val.count (· = 2)) = 1) ∧ ¬(st.val.contains 3) then 1
    else 0
  | 1 => if st.val.contains 4 then 6 else
            if st.val.contains 3 then 5 else
              if st.val.count (· == 2) = 2 then 4 else
                if st.val.contains 2 then 3 else 1
  | 2 => if st.val.contains 3 then 6 else
            if st.val.any (fun b => b == 2) (start := 1) then 5 else 3
  | 3 => if st.val.contains 2 then 6 else 5
  | 4 => 6
  | 5 => 6
  | _ => 0


def Hand.lt (x y : Hand) : Bool :=
  if x.type < y.type then true
  else if y.type < x.type then false
  else Hand.ltRule2 x y

/- # Parsing -/

@[inline]
def parseCard : Parsec Card := attempt do
  let c ← anyChar
  if ('2' ≤ c ∧ c ≤ '9') then
    let some x := charToCard c | fail "Oh no!"
    return x
  match c with
  | 'T' => return 9
  | 'J' => return 0
  | 'Q' => return 10
  | 'K' => return 11
  | 'A' => return 12
  | _ => fail "Card expected"

def parseHand : Parsec Hand := attempt do
  let c₁ ← parseCard
  let c₂ ← parseCard
  let c₃ ← parseCard
  let c₄ ← parseCard
  let c₅ ← parseCard
  return ⟨#[c₁, c₂, c₃, c₄, c₅], by simp⟩

def parseBid : Parsec (Hand × Nat) := do
  let hand ← parseHand
  ws
  let bid ← natNum
  return ⟨hand, bid⟩

/-
PART 2
-/

def secondPart (input : FilePath) : IO Nat := do
  let bids : Array (Hand × Nat) := (← IO.FS.lines input).foldl (init := #[])
    fun acc str => acc.push (str.yoloParse parseBid)
  let sorted : Array (Hand × Nat) := bids.qsort (Hand.lt ·.1 ·.1)
  return sorted.foldlIdx (init := 0)
    fun idx acc bid => acc + (idx + 1) * bid.2

--#eval secondPart Day07.testinput     --(ans: 5905)
--#eval secondPart Day07.realinput     --(ans: 249620106)

end Day07part2
