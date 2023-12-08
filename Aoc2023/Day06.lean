namespace Day06

def testinput : Array (Nat × Nat) := #[⟨7, 9⟩, ⟨15, 40⟩, ⟨30, 200⟩]
def realinput : Array (Nat × Nat) := #[⟨61, 430⟩, ⟨67, 1036⟩, ⟨75, 1307⟩, ⟨71, 1150⟩]

/-
PART 1:
-/

def numWins (T d : Nat) : Nat :=
  T.fold (init := 0) fun t acc => if t * (T - t) > d then acc+1 else acc

def firstPart (input : Array (Nat × Nat)) : IO Nat :=
  return input.foldl (init := 1) fun acc game => acc * numWins game.1 game.2

--#eval firstPart testinput
--#eval firstPart realinput

/-
PART 2:
-/

def testinput₂ : Nat × Nat := ⟨71530, 940200⟩
def realinput₂ : Nat × Nat := ⟨61677571, 430103613071150⟩

def secondPart (input : Nat × Nat) : IO Nat :=
  return numWins input.1 input.2

--#eval secondPart testinput₂
--#eval secondPart realinput₂    -- ~34 secs when interpreted, ~1s when compiled

end Day06
