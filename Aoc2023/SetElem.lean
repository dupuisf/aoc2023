/-! # SetElem class
-/

class SetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w))
    (dom : outParam (cont → idx → Prop)) where
  /--
  Like `GetElem.getElem` but for setting.

  Given a `mut` variable `arr` in a `do` block:
  * `set arr[i] := v`: proves the proof side goal by `get_elem_tactic`
  * `set arr[i]! := v`: panics `i` is out of bounds
  * `set arr[i]? := v`: does nothing if `i` is out of bounds
  * `set arr[i]'h := v`: uses `h` to prove the side goal
  -/
  setElem (xs : cont) (i : idx) (v : elem) (h : dom xs i) : cont

export SetElem (setElem)

@[never_extract]
private def outOfBounds [Inhabited α] : α :=
  panic! "index out of bounds"

/--
Set `xs[i] := v` or panic if `i` is out of bounds.
-/
@[inline] def setElem! [SetElem cont idx elem dom] (xs : cont) (i : idx) (v : elem) [Decidable (dom xs i)] : cont :=
  if h : _ then
    setElem xs i v h
  else
    have : Inhabited cont := ⟨xs⟩
    outOfBounds

/--
Set `xs[i] := v` if `i` is within bounds, otherwise do nothing.
-/
@[inline] def setElem? [SetElem cont idx elem dom] (xs : cont) (i : idx) (v : elem) [Decidable (dom xs i)] : cont :=
  if h : _ then setElem xs i v h else xs

declare_syntax_cat setExpr

syntax ident : setExpr
@[inherit_doc setElem] syntax ident noWs "[" term,+ "]" : setExpr
@[inherit_doc setElem] syntax ident noWs "[" term,+ "]'" term:max : setExpr
@[inherit_doc setElem] syntax ident noWs "[" term,+ "]" noWs "!" : setExpr
@[inherit_doc setElem] syntax ident noWs "[" term,+ "]" noWs "?" : setExpr

/-- Notation for updating a value. -/
syntax "set " setExpr " := " term : doElem

macro_rules
  | `(doElem| set $x:ident := $val) => `(doElem| $x:term := $val)
  | `(doElem| set $x:ident[$i] := $val) => `(doElem| $x:term := setElem $x $i $val (by get_elem_tactic))
  | `(doElem| set $x:ident[$i]'$h := $val) => `(doElem| $x:term := setElem $x $i $val $h)
  | `(doElem| set $x:ident[$i]! := $val) => `(doElem| $x:term := setElem! $x $i $val)
  | `(doElem| set $x:ident[$i]? := $val) => `(doElem| $x:term := setElem? $x $i $val)

-- Also support `set x[i1,i2,i3] := v` for `set x[(i1,i2,i3)] := v`
macro_rules
  | `(doElem| set $x:ident[$i,$is,*] := $val) => `(doElem| set $x:ident[($i,$is,*)] := $val)
  | `(doElem| set $x:ident[$i,$is,*]'$h := $val) => `(doElem| set $x:ident[($i,$is,*)]'$h := $val)
  | `(doElem| set $x:ident[$i,$is,*]! := $val) => `(doElem| set $x:ident[($i,$is,*)]! := $val)
  | `(doElem| set $x:ident[$i,$is,*]? := $val) => `(doElem| set $x:ident[($i,$is,*)]? := $val)
