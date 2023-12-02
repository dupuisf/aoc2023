import Lean.Data.Parsec
import Std.Data.Nat.Lemmas
import Std.Data.Array.Lemmas
import Init.Data.String.Basic
import Aoc2023.AesopExtra

namespace Char

def toNatDigit (c : Char) : Nat :=
  c.toNat - 48

end Char

namespace Array

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

def mkArray₂ (m n : Nat) (v : α) : Array (Array α) :=
  Array.mkArray m (Array.mkArray n v)

def foldtlM [Monad m] (f : β → α → m β) (init : β) (a : Array (Array α)) : m β :=
  a.foldlM (fun x row => row.foldlM f x) init

def foldtl (f : β → α → β) (init : β) (a : Array (Array α)) : β :=
  a.foldl (fun x row => row.foldl f x) init

def transpose [Inhabited α] (a : Array (Array α)) : Array (Array α) := Id.run do
  let dim := a.size
  let mut output : Array (Array α) := #[]
  for i in [0:dim] do
    let curCol := a.map (fun row => row[i]!)
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

def Pairwise (as : Array α) (r : α → α → Prop) :=
  ∀ i j : Nat, (hi : i < as.size) → (hj : j < as.size) → i ≠ j → r as[i] as[j]

def Nodup [DecidableEq α] (as : Array α) : Prop :=
  as.Pairwise (· ≠ ·)

-- FOR STD

theorem size_empty : (#[] : Array α).size = 0 := List.length_nil

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

/-- Ignore the result of the first parser called -/
@[inline] def andThen (p : Parsec α) (q : Unit → Parsec β) : Parsec β := do
  let _ ← p
  return (← q ())

instance : HAndThen (Parsec α) (Parsec β) (Parsec β) where
  hAndThen := Lean.Parsec.andThen

def fix (p : Parsec α → Parsec α) : Parsec α := fun it =>
  let p' : Parsec α := fun it' =>
    if it'.s.endPos - it'.i < it.s.endPos - it.i then
      fix p it'
    else
      .error it' "recursive call going backwards in the string"
  p p' it

def natNum : Parsec Nat := do
  let some n := (← manyChars digit).toNat? | fail "Not a natural number"
  return n

def natDigit : Parsec Nat := return (← digit).toNatDigit

def newlineChar : Parsec Unit := attempt do
  let c ← anyChar
  if c == '\u000a' || c == '\u000a' then return () else fail s!"Newline not found"

def eol : Parsec Unit := eof <|> (many1 newlineChar *> pure ())

partial def sepByCore (pcont : Parsec α) (psep : Parsec β) (acc : List α) :
  Parsec (List α) :=
(do let _ ← psep; sepByCore pcont psep (acc ++ [←pcont])) <|> pure acc

def sepBy (pcont : Parsec α) (psep : Parsec β) : Parsec (List α) :=
(do Parsec.sepByCore pcont psep [←pcont]) <|> pure []

def csv [Inhabited α] (p : Parsec α) : Parsec (List α) := sepBy p (do skipString ","; ws)

end Lean.Parsec
