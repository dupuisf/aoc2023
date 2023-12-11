import Lean.Data.Parsec
import Std.Data.Nat.Lemmas
import Std.Data.Array.Lemmas
import Std.Data.BitVec.Basic
import Init.Data.String.Basic
import Aoc2023.AesopExtra
import Aoc2023.SetElem

section general

def checkThat {α : Type _} (x : α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (p x)) :=
  if h : p x then some ⟨h⟩
  else none

def Array.checkThatAll {α : Type _} (xs : Array α) (p : α → Prop) [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < xs.size) → p xs[i])) :=
  match h : xs.all p with
  | false => none
  | true =>
      have hmain : ∀ (i : Fin xs.size), p xs[i] := by
        have htmp := (xs.all_eq_true _).mp h
        simpa [decide_eq_true_iff] using htmp
      some ⟨fun i hi => hmain ⟨i, hi⟩⟩

def Array.checkThatUpTo {α : Type _} (xs : Array α) (n : Nat) (hn : n ≤ xs.size) (p : α → Prop)
    [∀ a, Decidable (p a)] :
    Option (PLift (∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)))) :=
  if hzero : xs.size = 0 then
    have hmain : ∀ i, (h : i < n) → p (xs[i]'(Nat.lt_of_lt_of_le h hn)) := by
      intro i hi
      have : i < 0 := by
        calc i < n := hi
             _ ≤ xs.size := hn
             _ = 0 := hzero
      exact False.elim <| Nat.not_lt_zero i this
    some ⟨hmain⟩
  else
    match h : xs.all p (start := 0) (stop := n) with
    | false => none
    | true =>
        have hmain := by
          have htmp := (xs.all_iff_forall _ 0 n).mp h
          simpa [decide_eq_true_iff] using htmp
        have hmain' (i : Nat) (hi : i < n) : p (xs[i]'(Nat.lt_of_lt_of_le hi hn)) := by
          refine hmain ⟨i, Nat.lt_of_lt_of_le hi hn⟩ ?_
          exact hi
        some ⟨hmain'⟩

end general

namespace Char

def toNatDigit (c : Char) : Nat :=
  c.toNat - 48

end Char


abbrev Vec (n : Nat) (α : Type _) := { as : Array α // as.size = n }
abbrev Vec₂ (n m : Nat) (α : Type _) := Vec n (Vec m α)

instance instGetElemVec : GetElem (Vec n α) Nat α (fun _ i => i < n) where
  getElem xs i h := Array.get xs ⟨i, by rwa [xs.property]⟩

instance instGetElemVec₂ : GetElem (Vec₂ n m α) (Nat × Nat) α (fun _ i => i.1 < n ∧ i.2 < m) where
  getElem xs i h := (xs[i.1]'h.1)[i.2]'h.2

namespace Array

notation "Array₂ " α => Array (Array α)


def max [Inhabited α] [Max α] (a : Array α) : α :=
  if h : a.size = 0 then
    default
  else
    have : 0 < a.size := Nat.pos_of_ne_zero h
    a.foldl (init := a[0]) Max.max

def findIdx! (as : Array α) (p : α → Bool) : Nat :=
  match as.findIdx? p with
  | some x => x
  | none => panic!"Element not found"

def filterWithIdx (as : Array α) (p : Nat → α → Bool) : Array α :=
  (·.2) <| as.foldl (init := (0, Array.empty)) fun (idx, r) a =>
    if p idx a then
      (idx+1, r.push a)
    else
      (idx+1, r)

def foldlIdx (as : Array α) (f : Nat → β → α → β) (init : β) : β :=
  (as.foldl (β := β × Nat) (init := ⟨init, 0⟩) fun acc elem => ⟨f acc.2 acc.1 elem, acc.2 + 1⟩).1

def mkArray₂ (m n : Nat) (v : α) : Array (Array α) :=
  Array.mkArray m (Array.mkArray n v)

def foldtlM [Monad m] (f : β → α → m β) (init : β) (a : Array (Array α)) : m β :=
  a.foldlM (fun x row => row.foldlM f x) init

def foldtl (f : β → α → β) (init : β) (a : Array (Array α)) : β :=
  a.foldl (fun x row => row.foldl f x) init

def transpose [Inhabited α] (as : Array₂ α) : Option (Array₂ α) := do
  let dim := as.size
  if hdim : dim ≤ 0 then
    return #[]
  else
    have _ := Nat.lt_of_not_ge hdim
    let width := as[0].size
    let some ⟨_⟩ := as.checkThatAll fun row => row.size = width | failure
    let mut output : Array₂ α := #[]
    for i in [0:width] do
      let curCol := as.map (fun row => row[i]!)
      output := output.push curCol
    return output

def zipWith2D (a : Array (Array α)) (b : Array (Array β)) (f : α → β → γ) : Array (Array γ) :=
  a.zipWith b (fun ra rb => ra.zipWith rb f)

def modify₂ (a : Array (Array α)) (i j : Nat) (f : α → α) : Array (Array α) :=
  a.modify i (·.modify j f)

def set₂ (a : Array (Array α)) (i j : Nat) (x : α) : Array (Array α) :=
  a.modify i (·.modify j (fun _ => x))

def sum [Add α] [OfNat α 0] (a : Array α) : α := a.foldl (init := 0) (· + ·)

def containsAny (as : Array α) (p : α → Bool) : Bool := Id.run do
  for a in as do
    if p a then return true
  return false

def last (as : Array α) : Option α := as[as.size-1]?

def maybePush (as : Array α) (a? : Option α) : Array α :=
  match a? with
  | none => as
  | some x => as.push x

def best? (as : Array α) (keep : α → α → α) : Option α :=
  as.foldl (init := none) fun acc x => match acc with
                                       | none => some x
                                       | some z => some (keep z x)

def count (as : Array α) (p : α → Bool) : Nat :=
  as.foldl (init := 0) fun acc x => if p x then acc + 1 else acc

def natSet (as : Array α) (i : Nat) (v : α) (hi : i < as.size := by get_elem_tactic) : Array α :=
  Array.set as ⟨i, hi⟩ v

def getAllIdx (as : Array α) (p : α → Bool) : Array Nat :=
  as.foldlIdx (init := #[]) fun i ar elem => if p elem then ar.push i else ar

@[simp]
theorem size_natSet (as : Array α) (i : Nat) (v : α) {hi : i < as.size} :
    (as.natSet i v hi).size = as.size := Array.size_set _ _ _

instance instGetElemSubtype {n : Nat} :
    GetElem {as : Array α // as.size = n} Nat α fun _ i => LT.lt i n where
  getElem xs i h := xs.val.get ⟨i, by simp only [xs.property, h]⟩

def Pairwise (as : Array α) (r : α → α → Prop) :=
  ∀ i j : Nat, (hi : i < as.size) → (hj : j < as.size) → i ≠ j → r as[i] as[j]

def Nodup [DecidableEq α] (as : Array α) : Prop :=
  as.Pairwise (· ≠ ·)

instance instSetElem : SetElem (Array α) Nat α (fun as i => i < as.size) where
  setElem as i v h := as.set ⟨i, h⟩ v

--instance instSetElem₂ : SetElem (Array₂ α) (Nat × Nat) α
--    (fun as i => (h : i.1 < as.size) ∧ i.2 < (as.get ⟨i.1, h⟩).size) where
--  setElem as i v h := as.set ⟨i, h⟩ v

--instance instGetElem₂ : GetElem (Array₂ α) (Nat × Nat) α
--    (fun as i => if h : i.1 < as.size then i.2 < (as.get ⟨i.1, h⟩).size else False) where
--  getElem as i v h :=
--    as.get ⟨i.1, by simp [h]⟩ v

-- FOR STD

theorem size_empty : (#[] : Array α).size = 0 := List.length_nil

partial def binSearchIdx [Inhabited α] (as : Array α) (k : α) (lt : α → α → Bool)
    (lo := 0) (hi := as.size - 1) : Option Nat :=
  let rec go lo hi :=
    if lo ≤ hi then
      let m := (lo + hi)/2
      let a := as[m]!
      if lt a k then go (m+1) hi
      else if lt k a then
        if m == 0 then none
        else
          go lo (m-1)
      else some m
    else none
  if lo < as.size then
    let hi' := if hi < as.size then hi else as.size - 1
    go lo hi'
  else
    none
--termination_by go lo hi => hi - lo

def pop? (as : Array α) : Option α :=
  if h : as.size ≤ 0 then none
  else
    have : as.size - 1 < as.size := Nat.sub_one_lt_of_le (Nat.lt_of_not_le h) (Nat.le_refl _)
    as[as.size - 1]

def findIdx₂ {α : Type _} [Inhabited α] (xs : Array₂ α) (p : α → Bool) :
    Option (Nat × Nat) := do
  for i in [:xs.size] do
    for j in [:xs[i]!.size] do
      if p xs[i]![j]! then
        return ⟨i, j⟩
  failure

def findAllIdx {α : Type _} [Inhabited α] (xs : Array α) (p : α → Bool) :
    Array Nat := Id.run do
  xs.foldlIdx (init := #[]) fun idx acc x => if p x then acc.push idx else acc

def findAllIdx₂ {α : Type _} [Inhabited α] (xs : Array₂ α) (p : α → Bool) :
    Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for hi : i in [:xs.size] do
    have := hi.2
    for hj : j in [:xs[i].size] do
      have := hj.2
      if p xs[i][j] then
        out := out.push ⟨i, j⟩
  return out

end Array

namespace String

def toCharArray (s : String) : Array Char := s.data.toArray

def ofCharArray (a : Array Char) : String := { data := a.toList }

def reverse (s : String) : String :=
  s.foldr (init := "") fun c t => t.push c

def yoloParse [Inhabited α] (s : String) (p : Lean.Parsec α) : α :=
  match p s.iter with
  | Lean.Parsec.ParseResult.success _ x => x
  | Lean.Parsec.ParseResult.error _ _ => panic! "Parse error"

def parse? [Inhabited α] (s : String) (p : Lean.Parsec α) : Option α :=
  match p s.iter with
  | Lean.Parsec.ParseResult.success _ x => some x
  | Lean.Parsec.ParseResult.error _ _ => none

end String

/-- Simple set structure where we just put elements into an array. -/
structure ArraySet (α : Type _) [DecidableEq α] where
  content : Array α
  nodup : content.Nodup

namespace ArraySet

variable [DecidableEq α]

--def Any (p : α → Prop) (as : ArraySet α) : Prop :=
--  ∃ i, (h : i < as.content.size) → p as.content[i]

instance : Membership α (ArraySet α) where
  mem x as := x ∈ as.content

theorem mem_def (as : ArraySet α) (x : α) : x ∈ as ↔ x ∈ as.content := Iff.rfl

instance instDecidableMem {x : α} {as : ArraySet α} : Decidable (x ∈ as) :=
  inferInstanceAs (Decidable (x ∈ as.content))

--instance instDecidableMem {as : ArraySet α} : Decidable (Mem x as) :=

def mkEmpty : ArraySet α where
  content := #[]
  nodup := fun _ _ hi _ _ => by simp [Array.size_empty, Nat.not_lt_zero] at hi

def contains (as : ArraySet α) (x : α) : Bool := as.content.contains x

def card (as : ArraySet α) : Nat := as.content.size

theorem contains_iff (as : ArraySet α) (x : α) :
    as.contains x = true ↔ x ∈ as := by rw [contains]; exact Array.contains_def

theorem not_eq_getElem_of_not_mem (as : ArraySet α) {x : α} (hx : x ∉ as) :
    ∀ i, (h : i < as.content.size) → as.content[i] ≠ x := by
  intro i hi
  rw [mem_def, Array.mem_def, List.mem_iff_get, not_exists] at hx
  specialize hx ⟨i, hi⟩
  rwa [Array.getElem_eq_data_get]

theorem exists_getElem_of_mem (as : ArraySet α) {x : α} (hx : x ∈ as) :
    ∃ (i : Fin as.content.size), as.content[i] = x := by
  rw [mem_def, Array.mem_def, List.mem_iff_get] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  rwa [← Array.getElem_eq_data_get] at hi

def insert (as : ArraySet α) (x : α) : ArraySet α :=
  if hmem : x ∈ as then
    as
  else
    { content := as.content.push x,
      nodup := by
        unfold Array.Nodup Array.Pairwise
        intro i j hi hj hij
        simp only [Array.get_push]
        split
        case inl h =>
          split
          case inl h₂ => exact as.nodup i j h h₂ hij
          case inr h₂ =>
            have := not_eq_getElem_of_not_mem as hmem
            exact fun hmain => False.elim <| (this i h) hmain
        case inr h =>
          split
          case inl h₂ =>
            have := not_eq_getElem_of_not_mem as hmem
            exact fun hmain => False.elim <| (this j h₂) hmain.symm
          case inr h₂ =>
            rw [Array.size_push, ←Nat.succ_eq_add_one, Nat.lt_succ] at hi hj
            aesop }

end ArraySet

namespace Lean.Parsec

def fix (p : Parsec α → Parsec α) : Parsec α := fun it =>
  let p' : Parsec α := fun it' =>
    if it'.s.endPos - it'.i < it.s.endPos - it.i then
      fix p it'
    else
      .error it' "recursive call going backwards in the string"
  p p' it

@[inline]
def natNum : Parsec Nat := attempt do
  let some n := (← manyChars digit).toNat? | fail "Not a natural number"
  return n

@[inline]
def natDigit : Parsec Nat := attempt do return (← digit).toNatDigit

@[inline]
def alphanum : Parsec Char := attempt do
  let c ← anyChar
  if '0' ≤ c ∧ c ≤ '9' then return c
  if 'a' ≤ c ∧ c ≤ 'z' then return c
  if 'A' ≤ c ∧ c ≤ 'Z' then return c
  fail s!"alphanumeric character expected"

def newlineChar : Parsec Unit := attempt do
  let c ← anyChar
  if c == '\u000a' || c == '\u000a' then return () else fail "Newline not found"

def eol : Parsec Unit := eof <|> (many1 newlineChar *> pure ())

partial def sepByCore (pcont : Parsec α) (psep : Parsec β) (acc : List α) :
  Parsec (List α) :=
attempt (do let _ ← psep; sepByCore pcont psep (acc ++ [←pcont])) <|> pure acc

def sepBy (pcont : Parsec α) (psep : Parsec β) : Parsec (List α) :=
(do Parsec.sepByCore pcont psep [←pcont]) <|> pure []

partial def sepByACore (pcont : Parsec α) (psep : Parsec β) (acc : Array α) :
  Parsec (Array α) :=
attempt (do let _ ← psep; sepByACore pcont psep (acc.push (←pcont))) <|> pure acc

def sepByA (pcont : Parsec α) (psep : Parsec β) : Parsec (Array α) :=
(do Parsec.sepByACore pcont psep #[←pcont]) <|> pure #[]

def csv [Inhabited α] (p : Parsec α) : Parsec (List α) := sepBy p (do skipString ","; ws)

/-- At least one space -/
def whites : Parsec Unit := do
  let _ ← (pchar ' ')
  let _ ← manyChars (pchar ' ')
  return ()

end Lean.Parsec

namespace Std.BitVec

def foldls (v : BitVec n) (f : α → Bool → α) (init : α) : α :=
  n.fold (init := init) fun i acc => f acc (v.getLsb i)

def foldlsIdx (v : BitVec n) (f : Nat → α → Bool → α) (init : α) : α :=
  n.fold (init := init) fun i acc => f i acc (v.getLsb i)

def setPos (v : BitVec n) (i : Nat) (b : Bool) : BitVec n :=
  let mask := (1 : BitVec n).shiftLeft i
  if b then
    v ||| mask
  else
    let mask' := BitVec.allOnes n ^^^ mask    -- Xor
    v &&& mask'

end Std.BitVec

-- ********
-- * MISC *
-- ********

class Foldable (cont : Type u) (elem : Type v) where
  fold : cont → (α → elem → α) → α → α

export Foldable (fold)

class Container (cont : Type u) (idx : Type v) (elem : outParam (Type w))
    (dom : outParam (cont → idx → Prop))
    [GetElem cont idx elem dom] [SetElem cont idx elem dom] [Foldable cont elem] where
