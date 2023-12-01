import Aoc2023.Utils
import Std.Data.RBMap.Basic

open Std

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

inductive Lettre
| a
| b
| c
deriving BEq, Repr

instance : ToString Lettre where
  toString x := match x with
                | .a => "a"
                | .b => "b"
                | .c => "c"

instance : Mul Lettre where
  mul x y := match x, y with
             | .a, .a => .c
             | .a, .b => .c
             | .a, .c => .a
             | .b, .a => .c
             | .b, .b => .b
             | .b, .c => .a
             | .c, .a => .a
             | .c, .b => .c
             | .c, .c => .c

def Lettre.cmp : Lettre → Lettre → Ordering
| .a, .a => .eq
| .a, .b => .lt
| .a, .c => .lt
| .b, .a => .gt
| .b, .b => .eq
| .b, .c => .lt
| .c, .a => .gt
| .c, .b => .gt
| .c, .c => .eq

def mulSets (xs ys : RBSet Lettre Lettre.cmp) : RBSet Lettre Lettre.cmp := Id.run do
  let mut out := mkRBSet Lettre Lettre.cmp
  for x in xs do
    for y in ys do
      if ¬out.contains (x*y) then
        out := out.insert <| x * y
  return out

def fillTable (input : Array Lettre) : Array (Array (Array Lettre)) := Id.run do
  let n := input.size
  let mut table : Array (Array (Array Lettre)) := #[input.map fun x => #[x]]
  for len in [2:n+1] do
    let mut curRow : Array (Array Lettre) := #[]
    for startPos in [0:n-len] do
      let mut curPos : Array Lettre := #[]
      for pos in [0:len-1] do
        curPos := curPos.push <| mulSets table[pos]![startPos]! table[len-(pos+1)-1]![startPos+pos+1]!
        dbg_trace s!"len = {len}, startPos = {startPos}, curPos = {curPos}"
      curRow := curRow.push curPos
    table := table.push curRow
  return table

#eval mulSets #[.b] #[.a, .b]
#eval fillTable #[.b, .b, .b, .b, .a]

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
