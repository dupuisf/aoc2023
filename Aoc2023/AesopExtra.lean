import Aesop

--@[aesop safe forward]
--theorem Nat.eq_of_le_of_not_lt {n m : Nat} (h₁ : n ≤ m) (h₂ : ¬(n < m)) : n = m :=
--  Or.casesOn (Nat.eq_or_lt_of_le h₁) id (fun h => False.elim <| h₂ h)

@[aesop safe forward]
theorem Nat.eq_of_le_of_le {n m : Nat} (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  simp [Nat.le_antisymm_iff, h₁, h₂]

attribute [aesop safe forward] Nat.le_of_lt_succ

