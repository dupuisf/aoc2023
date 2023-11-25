import Aoc2023.Utils

--def produitChaine (r c : Array Nat) : Array (Array Nat) := Id.run do
--  --if rows.size ≠ cols.size then panic!
--  let n := r.size
--  let mut m := Array.mkArray (n+1) (Array.mkArray (n+1) 1000000)
--  for i in [0:n+1] do
--    m := m.modify₂ i i (fun _ => 0)
--  for k in [1:n] do
--    for i in [1:n-k+1] do
--      for ℓ in [i+1:i+k+1] do
--        if m[i]![i+k]! > m[i]![ℓ-1]! + m[ℓ]![i+k]! + r[i]! * c[i+k]!* r[ℓ]!
--          then m := m.modify₂ i (i+k) (fun _ => m[i]![ℓ-1]! + m[ℓ]![i+k]! + r[i]! * c[i+k]!* r[ℓ]!)
--  return m
--
--#eval produitChaine #[0, 10, 30, 5, 60, 3] #[0, 30, 5, 60, 3, 8]

structure Dummy where
  func : Nat → Nat

def main (_ : List String) : IO Unit := do
  let mut a : Array Dummy := Array.mkArray 3 ⟨id⟩
  for rnd in [0:1000000] do
    if rnd % 500 == 0 then IO.println s!"{rnd}"
    if rnd % 2 = 0 then
      a := a.modify 0 (fun x => ⟨x.1⟩)
    else
      a := a.modify 0 (fun x => ⟨x.1⟩)
