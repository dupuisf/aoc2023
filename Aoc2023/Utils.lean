import Lean.Data.Parsec
import Std.Data.Nat.Lemmas
import Std.Data.Array.Lemmas
import Std.Data.BitVec.Basic
import Init.Data.String.Basic
import Aoc2023.AesopExtra
--import Aoc2023.SetElem

notation "Array₂ " α => Array (Array α)

def Fin.addNat' (x : Fin n) (i : Nat) : Fin n where
  val := (x + i) % n
  isLt := by cases n with
          | zero => exact Fin.elim0 x
          | succ k => exact Nat.mod_lt _ <| Nat.zero_lt_succ _


instance Fin.instHAddFin : HAdd (Fin n) Nat (Fin n) where
  hAdd x y := ⟨(x + y) % n, by cases n with
                            | zero => exact Fin.elim0 x
                            | succ k => exact Nat.mod_lt _ <| Nat.zero_lt_succ _⟩

theorem Membership.mem_upper {i a b step : Nat} (h : i ∈ (⟨a, b, step⟩ : Std.Range)) : i < b := h.2

macro_rules
| `(tactic|get_elem_tactic_trivial) => `(tactic|exact Membership.mem_upper ‹_›)

attribute [aesop safe forward] Nat.not_lt_zero

namespace Nat

@[aesop safe forward]
theorem sub_one_lt_self {a : Nat} (ha : 0 < a) : a - 1 < a :=
  sub_one_lt_of_le ha (Nat.le_refl _)

end Nat

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


def Vec (n : Nat) (α : Type _) := { as : Array α // as.size = n }
def Vec₂ (n m : Nat) (α : Type _) :=
  { as : Array₂ α // as.size = n ∧ ∀ (i : Nat) (hi : i < as.size), as[i].size = m}

instance instGetElemVec : GetElem (Vec n α) Nat α (fun _ i => i < n) where
  getElem xs i h := Array.get xs.val ⟨i, by rwa [xs.property]⟩

--instance instGetElemVec₂ : GetElem (Vec₂ n m α) (Nat × Nat) α (fun _ i => i.1 < n ∧ i.2 < m) where
--  getElem xs i h :=
--    have h₁ : i.1 < xs.val.size := by rw [xs.property.1]; exact h.1
--    have h₂ := h.2
--    have hmain : i.2 < xs.val[i.1].size := by rwa [xs.property.2 i.1 h₁]
--    xs.val[i.1][i.2]

instance instBEqVec [BEq α] : BEq (Vec n α) where
  beq x y := x.val == y.val

instance instInhabitedVec [Inhabited α] : Inhabited (Vec n α) :=
  ⟨⟨Array.mkArray n default, by rw [Array.size_mkArray]⟩⟩

namespace Array

def toVec (as : Array α) : Σ n : Nat, (Vec n α) :=
  ⟨as.size, ⟨as, rfl⟩⟩

def toVec₂ (as : Array₂ α) : Option (Σ (n m : Nat), Vec₂ n m α) := do
  if h : 0 < as.size then
    let m := as[0].size
    let n := as.size
    let some ⟨hmain⟩ := as.checkThatAll (fun row => row.size = m) | failure
    return ⟨n, m, as, ⟨rfl, hmain⟩⟩
  else
    return ⟨0, 0, #[], by
      refine ⟨by simp, fun i hi => ?_⟩
      simp at hi
      aesop (add safe forward Nat.not_lt_zero)⟩

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

def get₂! [Inhabited α] (a : Array₂ α) (i j : Nat) : α :=
  (a.get! i).get! j

def set₂ (a : Array (Array α)) (i j : Nat) (x : α) : Array (Array α) :=
  a.modify i (·.modify j (fun _ => x))

def sum [Add α] [OfNat α 0] (a : Array α) : α := a.foldl (init := 0) (· + ·)

def containsAny (as : Array α) (p : α → Bool) : Bool := Id.run do
  for a in as do
    if p a then return true
  return false

def last? (as : Array α) : Option α := as[as.size-1]?

def last (as : Array α) (h : 0 < as.size) : α :=
  as[as.size-1]'(by aesop)

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

--instance instSetElem : SetElem (Array α) Nat α (fun as i => i < as.size) where
--  setElem as i v h := as.set ⟨i, h⟩ v

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

def addWallTopBottom (grid : Array₂ α) (x : α) : Array₂ α :=
  if h : 0 < grid.size then
    let topWidth := grid[0].size
    let bottomWidth := (grid.last h).size
    #[mkArray topWidth x] ++ grid ++ #[mkArray bottomWidth x]
  else
    #[]

def addWallLeftRight (grid : Array₂ α) (x : α) : Array₂ α :=
  grid.foldl (init := #[]) fun acc row => acc.push <| (#[x] ++ row).push x

def addWall (grid : Array₂ α) (x : α) : Array₂ α :=
  grid.addWallLeftRight x |>.addWallTopBottom x

-- For std
@[simp] theorem getElem_mkArray {n : Nat} {a : α} {i : Nat} {hi : i < n} :
    have : i < (mkArray n a).size := by simp [size_mkArray, hi]
    (mkArray n a)[i] = a := by
  simp only [mkArray, Array.getElem_eq_data_get, List.get_replicate]

end Array

namespace Vec

def mkVec (n : Nat) (a : α) : Vec n α where
  val := Array.mkArray n a
  property := by rw [Array.size_mkArray]

def empty : Vec 0 α where
  val := #[]
  property := by simp

def map {n : Nat} (xs : Vec n α) (f : α → β) : Vec n β :=
  ⟨xs.val.map f, by rw [Array.size_map, xs.property]⟩

def foldl (xs : Vec n α) (init : β) (f : β → α → β) : β := xs.val.foldl (init := init) f

def range (n : Nat) : Vec n Nat where
  val := Array.range n
  property := Array.size_range

def rangeFin (n : Nat) : Vec n (Fin n) where
  val := (Array.range n).mapIdx fun i _ => ⟨i, by have := i.2; have h₂ := Array.size_range (n := n); simpa [h₂] using this⟩
  property := by rw [Array.size_mapIdx, Array.size_range]

def foldlIdx (xs : Vec n α) (init : β) (f : Fin n → β → α → β) : β :=
  match n with
  | 0 => init
  | k+1 => (xs.foldl (β := β × (Fin (k+1))) (init := ⟨init, 0⟩) fun acc elem => ⟨f acc.2 acc.1 elem, acc.2 + 1⟩).1

@[simp] theorem size_val {xs : Vec n α} : xs.val.size = n := xs.property

def zipWith (as : Vec n α) (bs : Vec n β) (f : α → β → γ) : Vec n γ where
  val := (Array.range n).mapIdx fun i _ => f as[i] bs[i]
  property := by rw [Array.size_mapIdx, Array.size_range]

def zip (as : Vec n α) (bs : Vec n β) : Vec n (α × β) := as.zipWith bs Prod.mk

def set (as : Vec n α) (i : Fin n) (a : α) : Vec n α :=
  let i' : Fin as.val.size := ⟨i.val, by simp [as.property]⟩
  ⟨as.val.set i' a, by rw [Array.size_set, size_val]⟩

def set! (as : Vec n α) (i : Nat) (a : α) :=
  if h : i < n then
    let h' : i < as.val.size := by rwa [size_val]
    ⟨as.val.set ⟨i, h'⟩ a, by rw [Array.size_set, size_val]⟩
  else
    as

def reverse (as : Vec n α) : Vec n α where
  val := as.val.reverse
  property := by rw [Array.size_reverse, as.property]

end Vec

namespace Vec₂

instance instBEqVec₂ [BEq α] : BEq (Vec₂ n m α) where
  beq x y := x.val == y.val

def empty : Vec₂ 0 0 α where
  val := #[]
  property := ⟨by simp, fun i hi => by simp [Nat.not_lt_zero] at hi⟩

def mkVec₂ (n m : Nat) (a : α) : Vec₂ n m α where
  val := Array.mkArray₂ n m a
  property := by
    refine ⟨by rw [Array.mkArray₂, Array.size_mkArray], ?_⟩
    intro i hi
    rw [Array.mkArray₂, Array.size_mkArray] at hi
    simp only [Array.mkArray₂, Array.getElem_mkArray (hi := hi), Array.size_mkArray]

instance instInhabitedSigma [Inhabited α] : Inhabited (Σ n m, Vec₂ n m α) :=
  ⟨0, 0, empty⟩

instance instInhabitedVec₂ [Inhabited α] : Inhabited (Vec₂ n m α) :=
  ⟨mkVec₂ n m default⟩

def ofVecVec (grid : Vec n (Vec m α)) : Vec₂ n m α where
  val := grid.val.map (·.val)
  property := by
    refine ⟨?_, ?_⟩
    · rw [Array.size_map, grid.property]
    · intro i hi
      rw [Array.getElem_map]
      rw [Array.size_map, grid.property] at hi
      exact grid[i].property

def map {n m : Nat} (grid : Vec₂ n m α) (f : α → β) : Vec₂ n m β where
  val := grid.val.map (·.map f)
  property := by
    refine ⟨?_, fun i hi => ?_⟩
    · rw [Array.size_map, grid.property.1]
    · rw [Array.size_map] at hi
      rw [Array.getElem_map, Array.size_map]
      exact grid.property.2 i hi

@[simp]
theorem size_val (as : Vec₂ n m α) : as.val.size = n := by rw [as.property.1]

@[simp]
theorem size_val_get_fin (as : Vec₂ n m α) (i : Fin as.val.size) : as.val[i].size = m := by
  simp [as.property.2]

@[simp]
theorem size_val_get (as : Vec₂ n m α) (i : Nat) {hi : i < n} :
    (as.val[i]'(by simp [hi])).size = m := by
  simp [as.property.2]

def getRow (grid : Vec₂ n m α) (i : Nat) (hi : i < n) : Vec m α where
  val :=
    have hi' : i < grid.val.size := by rw [grid.property.1]; exact hi
    grid.val[i]
  property := grid.property.2 i _

instance instGetElemNatVec₂ : GetElem (Vec₂ n m α) Nat (Vec m α) (fun _ i => i < n) where
  getElem xs i hi := xs.getRow i hi

def toArrayVec (grid : Vec₂ n m α) : Array (Vec m α) :=
  grid.val.mapIdx fun ⟨i, hi⟩ _ => grid.getRow i (by rwa [← grid.property.1])

@[simp]
theorem size_toArrayVec (grid : Vec₂ n m α) : grid.toArrayVec.size = n := by
  rw [toArrayVec, Array.size_mapIdx, grid.property.1]

def toVecVec (grid : Vec₂ n m α) : Vec n (Vec m α) where
  val := grid.toArrayVec
  property := grid.size_toArrayVec

def getCol (grid : Vec₂ n m α) (i : Nat) (hi : i < m) : Vec n α where
  val := grid.val.mapIdx fun ⟨j, hj⟩ _ => (grid.getRow j (by rwa [← grid.property.1]))[i]
  property := by rw [Array.size_mapIdx, grid.property.1]

def transpose (grid : Vec₂ n m α) : Vec₂ m n α where
  val :=
    (Array.range m).mapIdx fun ⟨j, hj⟩ _ => (grid.getCol j (by rwa [Array.size_range] at hj)).val
  property := by
    refine ⟨by rw [Array.size_mapIdx, Array.size_range], fun i hi => ?_⟩
    rw [Array.getElem_mapIdx, Vec.size_val]

def set (as : Vec₂ n m α) (i : Fin n) (j : Fin m) (a : α) : Vec₂ n m α :=
  let i' : Fin as.val.size := ⟨i, by simp [as.property.1]⟩
  let j' : Fin as.val[i'].size := ⟨j, by simp⟩
  ⟨as.val.set i' (as.val[i].set j' a), by
    refine ⟨by simp, ?_⟩
    intro k hk
    simp at hk
    rw [Array.get_set]
    · split
      case inl h =>
        simp [Array.size_set]

      case inr h => simp [as.property.2, hk]
    · rwa [as.property.1]⟩

def set! (as : Vec₂ n m α) (i j : Nat) (a : α) :=
  if hi : i < n then
    if hj : j < m then
      let hi' : i < as.val.size := by rwa [as.property.1]
      let hj' : j < as.val[i].size := by rwa [as.property.2]
      ⟨as.val.set ⟨i, hi'⟩ (as.val[i].set ⟨j, hj'⟩ a), by
        refine ⟨?_, ?_⟩
        rw [Array.size_set, as.property.1]
        intro k hk
        have hk' : k < as.val.size := by rwa [Array.size_set] at hk
        rw [Array.get_set]
        by_cases H : i = k <;> simp [H, as.property.2 k hk']
        exact hk'⟩
    else as
  else as

def getD (as : Vec₂ n m α) (i j : Nat) (d : α) : α :=
  if h : i < n ∧ j < m then
    have hi := h.1
    have hj := h.2
    as[i][j]
  else d

def rotateCW (grid : Vec₂ n m α) : Vec₂ m n α where
  val :=
    (Array.range m).mapIdx fun ⟨j, hj⟩ _ => (grid.getCol j (by rwa [Array.size_range] at hj)).reverse.val
  property := by
    refine ⟨by rw [Array.size_mapIdx, Array.size_range], fun i hi => ?_⟩
    rw [Array.getElem_mapIdx, Vec.size_val]

def rotateCCW (grid : Vec₂ n m α) : Vec₂ m n α where
  val :=
    have : ∀ j, j < m → m - j - 1 < m := fun j hj => by
      rw [Nat.sub_sub]
      exact Nat.sub_lt_self (Nat.zero_lt_succ _) <| Nat.succ_le_of_lt hj
    (Array.range m).mapIdx fun ⟨j, hj⟩ _ => (grid.getCol (m-j-1) (this j (by rwa [Array.size_range] at hj))).reverse.val
  property := by
    refine ⟨by rw [Array.size_mapIdx, Array.size_range], fun i hi => ?_⟩
    rw [Array.getElem_mapIdx, Vec.size_val]

end Vec₂

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

namespace List

def sum [Add α] [OfNat α 0] (as : List α) : α :=
  as.foldl (init := 0) (· + ·)

end List

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

def anyCharThat (p : Char → Bool) : Parsec Char := attempt do
  let c ← anyChar
  if p c then return c else fail "Character doesn't satisfy p"

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

--class Container (cont : Type u) (idx : Type v) (elem : outParam (Type w))
--    (dom : outParam (cont → idx → Prop))
--    [GetElem cont idx elem dom] [SetElem cont idx elem dom] [Foldable cont elem] where
