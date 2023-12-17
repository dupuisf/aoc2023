
inductive Direction
| n | w | e | s
deriving BEq, Repr, DecidableEq

instance Direction.instToStringDirection : ToString Direction where
  toString dir :=
    match dir with
    | .n => "N" | .w => "W" | .e => "E" | .s => "S"

instance Direction.instHAddIntProd : HAdd (Int × Int) Direction (Int × Int) where
  hAdd x y := match y with
              | .n => ⟨x.1-1, x.2⟩ | .w => ⟨x.1, x.2 - 1⟩ | .e => ⟨x.1, x.2 + 1⟩ | .s => ⟨x.1+1, x.2⟩

def Direction.left : Direction → Direction
| .n => .w | .w => .s | .s => .e | .e => .n

def Direction.right : Direction → Direction
| .n => .e | .w => .n | .s => .w | .e => .s

def Direction.flip : Direction → Direction
| .n => .s | .w => .e | .s => .n | .e => .w

def Direction.foldM {m : Type _ → Type _} [Monad m] (init : α) (f : α → Direction → m α) : m α := do
  let n ← f init .n
  let w ← f n .w
  let e ← f w .e
  let s ← f e .s
  return s

def Direction.fold (init : α) (f : α → Direction → α) : α :=
  Id.run <| Direction.foldM init f
