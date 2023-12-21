import Aoc2023.Utils
import Std.Data.HashMap.Basic
import Std.Data.HashMap.WF

open System Lean Lean.Parsec

macro "derive_ToString" t:term : command =>
  `(instance : ToString $t where toString := Std.Format.pretty ∘ repr)

namespace Day20

def testinput1 : FilePath := "/home/fred/lean/aoc2023/input_20_test1"
def testinput2 : FilePath := "/home/fred/lean/aoc2023/input_20_test2"
def realinput : FilePath := "/home/fred/lean/aoc2023/input_20"

/-
PART 1:
-/

inductive ModuleType
| broadcaster
| conj
| flipflop
deriving BEq, Repr, DecidableEq, Inhabited

structure Module where
  nm : String
  ty : ModuleType
  dest : List String
  parentStates : Std.HashMap String Bool
  onOff : Bool
deriving Inhabited

structure Pulse where
  orig : String
  dest : String
  ty : Bool
deriving BEq, Repr, DecidableEq, Inhabited

def parseModuleName : Parsec (String × ModuleType) :=
  (attempt do skipString "%"; let name ← word; return ⟨name, .flipflop⟩)
  <|> (attempt do skipString "&"; let name ← word; return ⟨name, .conj⟩)
  <|> (attempt do let name ← pstring "broadcaster"; return ⟨name, .broadcaster⟩)

def parseModule : Parsec (String × ModuleType × List String) := do
  let ⟨name, ty⟩ ← parseModuleName
  skipString " -> "
  let dest ← sepBy word (pstring ", ")
  return ⟨name, ty, dest⟩

structure Env where
  modules : Std.HashMap String Module
  pulses : Std.Queue Pulse
  clockHi : Nat
  clockLo : Nat
  buttonsLeft : Nat

abbrev PulseM := StateM Env

def popPulse : PulseM (Option Pulse) := do
  let env ← get
  match env.pulses.dequeue? with
  | none => return none
  | some ⟨⟨orig, dest, true⟩, q'⟩ =>
      set { env with pulses := q', clockHi := env.clockHi+1 }
      return some ⟨orig, dest, true⟩
  | some ⟨⟨orig, dest, false⟩, q'⟩ =>
      set { env with pulses := q', clockLo := env.clockLo+1 }
      return some ⟨orig, dest, false⟩

def getClockHi : PulseM Nat := do let env ← get; return env.clockHi
def getClockLo : PulseM Nat := do let env ← get; return env.clockLo
def getResult : PulseM Nat := do
  let hi ← getClockHi
  let lo ← getClockLo
  return hi * lo

def getModule (nm : String) : PulseM Module := do
  let env ← get
  match env.modules.find? nm with
  | none => panic! s!"Module not found, name : {nm}"
  | some m => return m

def setParentsState (nm : String) (parent : String) (st : Bool) : PulseM Unit := do
  let env ← get
  let some oldmodule := env.modules.find? nm | panic! "Problem"
  let newmodule : Module := { oldmodule with parentStates := oldmodule.parentStates.modify parent (fun _ _ => st) }
  let newmodules := env.modules.modify nm (fun _ _ => newmodule)
  set { env with modules := newmodules }

def flip (nm : String) : PulseM Unit := do
  let env ← get
  let some oldmodule := env.modules.find? nm | panic! "Problem"
  let newmodule : Module := { oldmodule with onOff := !oldmodule.onOff }
  let newmodules := env.modules.modify nm (fun _ _ => newmodule)
  set { env with modules := newmodules }

def sendPulse (orig : String) (ty : Bool) (dests : List String) : PulseM Unit := do
  let env ← get
  let newpulses : List Pulse := dests.foldl (init := []) fun acc d => ⟨orig, d, ty⟩ :: acc
  set { env with pulses := env.pulses.enqueueAll newpulses }

def handlePulse (p : Pulse) : PulseM Unit := do
  let m ← getModule p.dest
  let destlist := m.dest
  match m.ty with
  | .broadcaster => sendPulse p.dest p.ty destlist
  | .conj =>
      setParentsState p.dest p.orig p.ty
      let m ← getModule p.dest
      let allhi : Bool := m.parentStates.fold (init := true) fun acc _ st => acc && st
      sendPulse p.dest (!allhi) destlist
  | .flipflop =>
      if !p.ty then
        flip p.dest
        sendPulse p.dest (!m.onOff) destlist

def getButtonsLeft : PulseM Nat := do
  let env ← get
  return env.buttonsLeft

def decButton : PulseM Unit := do
  let env ← get
  set { env with buttonsLeft := env.buttonsLeft - 1 }

partial def exec : PulseM Nat := do
  let curpulse ← popPulse
  match curpulse with
    | none =>
        match (← getButtonsLeft) with
        | 0 => return (← getResult)
        | _k+1 =>
            decButton
            sendPulse "broadcaster" false ["broadcaster"]
            return (← exec)
    | some p =>
        --dbg_trace s!"orig : {p.1}, dest : {p.2}, type : {p.3}"
        handlePulse p
        return (← exec)

def PulseM.run (env : Env) : Nat := StateT.run' exec env

def findParents (nm : String) (modules : Array (String × ModuleType × List String)) :
    List String :=
  modules.foldl (init := []) fun acc m =>
    let dest := m.2.2
    match dest.find? (· == nm) with
    | none => acc
    | some _ => m.1 :: acc

def firstPart (input : FilePath) : IO String := do
  let some moduleList := (← IO.FS.lines input).mapM (m := Option) (fun s => s.parse? parseModule)
    | return "Parse error"
  let parentsList : Array (String × List String) := moduleList.map (fun m => ⟨m.1, findParents m.1 moduleList⟩)
  IO.println parentsList
  let parentsList' : Array (String × (Std.HashMap String Bool)) :=
    parentsList.map fun ⟨nm, pars⟩ => ⟨nm, Std.HashMap.ofList (pars.map fun s => (⟨s, false⟩ : String × Bool))⟩
  let parentsHashMap : Std.HashMap String (Std.HashMap String Bool) :=
    Std.HashMap.ofList parentsList'.data
  let initModules : Array Module := moduleList.map
    fun m => ⟨m.1, m.2.1, m.2.2, parentsHashMap.find! m.1, false⟩
  let initModulesLst : List (String × Module) := initModules.data.map fun m => ⟨m.1, m⟩
  let initEnv : Env :=
    { modules := Std.HashMap.ofList initModulesLst
      pulses := Std.Queue.empty
      clockHi := 0
      clockLo := 0
      buttonsLeft := 1000 }
  --let modules : Std.HashMap String Module :=
  --  Std.HashMap.ofList <| moduleList.data.foldl (init := []) fun acc x => ⟨x.nm, x⟩ :: acc
  return s!"{PulseM.run initEnv}"

--#eval firstPart testinput1           --(ans: )
--#eval firstPart realinput           --(ans: )

/-
PART 2:
-/

def secondPart (input : FilePath) : IO String := do
  let rawdata := (← IO.FS.lines input)
  return s!"bla"

--#eval secondPart testinput1           --(ans: )
--#eval secondPart realinput           --(ans: )

end Day20
