import InvLimDiss.CFSL.Cocontinous

open Syntax Semantics

variable {Vars : Type}

def Path (c : Program Vars) (s : State Vars) : Type :=
  { list : List ((Program Vars) × (State Vars)) | ∃ list', list = (c, s)::list' }

def Path.length {c : Program Vars} {s : State Vars} (path : Path c s) := path.1.length
def Path.get {c : Program Vars} {s : State Vars} (path : Path c s) := path.1.get

def Scheduler : Type :=
  { scheduler : Program Vars → State Vars → Action | ∀ c s, scheduler c s ∈ enabledAction c s}

def forwardSemantics (c : Program Vars) (s : State Vars) : unitInterval :=
  sInf {∑' path : Path c s, ∏' i : Fin path.length,
    if h : i ≥ path.length then 1 else
    programSmallStepSemantics
      (path.get i).1 (path.get i).2
      (scheduler.1 (path.get i).1 (path.get i).2)
      (path.get (⟨i+1, sorry⟩)).1 (path.get (⟨i+1, sorry⟩)).2
  | scheduler : Scheduler }
