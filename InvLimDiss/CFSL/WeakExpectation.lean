import InvLimDiss.CFSL.Step
import InvLimDiss.SL.Fuzzy
import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.Program.AtomicFinal
import Mathlib.Order.FixedPoints

/-! This file contains the concurrent bellman-fixpoint and lemmas about, especially
  * `wrleStep` the concurrent bellman-operator
  * `wrleStep_mono` the concurrent bellman-operator is monotone
  * `wrle'` the fixpoint of the concurrent bellman-equation
  * `wrle_def` one unfolding of the bellman-solution

  We also offer syntax as `wrle` in the fsl environment. -/

namespace CFSL

open FSL Syntax OrderHom unitInterval Atom Semantics

variable {Var : Type}

/-- The concurrent bellman-operator.-/
noncomputable def wrleStep (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[fsl| fFalse]
  | X, program => `[fsl| [[resource]] -⋆ [[step program (fun c => `[fsl| [[X c]] ⋆ [[resource]] ]) ]] ]

theorem wrleStep_mono (post : StateRV Var) (resource : StateRV Var) : Monotone (wrleStep post resource) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro c
  unfold wrleStep
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply fslSepDiv_mono le_rfl
    apply step_mono
    rw [Pi.le_def]
    intro c
    rw [Pi.le_def]
    intro s
    apply fslSepMul_mono
    · rw [Pi.le_def] at h_X
      exact h_X c
    · exact le_rfl

/-- wrleStep as a monotone function -/
noncomputable def wrleStepHom (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) →o (Program Var → StateRV Var) :=
  ⟨wrleStep post resource, wrleStep_mono post resource⟩

/-- The greatest solution to the concurrent bellman equation -/
noncomputable def wrle' (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :=
  gfp (wrleStepHom post resource) program

syntax "wrle [" term "] (" fsl " | " fsl ")" : fsl
macro_rules
  | `(term| `[fsl| wrle [$c:term] ($p:fsl | $r:fsl)]) => `(wrle' $c `[fsl| $p] `[fsl| $r])
  | `(term| `[fsl $v| wrle [$c:term] ($p:fsl | $r:fsl)]) => `(wrle' $c `[fsl $v| $p] `[fsl $v| $r])


syntax "wrle [" program "] (" fsl " | " fsl ")" : fsl
macro_rules
  | `(term| `[fsl| wrle [$c:program] ($p:fsl | $r:fsl)]) =>
    `(wrle' [Prog| $c] `[fsl| $p] `[fsl| $r])
  | `(term| `[fsl $v| wrle [$c:program] ($p:fsl | $r:fsl)]) =>
    `(wrle' [Prog| $c] `[fsl $v| $p] `[fsl $v| $r])

open Lean PrettyPrinter Delaborator

def makeBrackets [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

@[app_unexpander wrle']
def unexpanderwrle : Unexpander
  | `($_ [Prog| $c:program] $p $r) =>
      do `(`[fsl| wrle [$c:program] ($(← makeBrackets p):fsl | $(← makeBrackets r):fsl )])
  | `($_ $c:term $p $r) =>
      do `(`[fsl| wrle [$c:term] ($(← makeBrackets p):fsl | $(← makeBrackets r):fsl )])
  | _ => throw ()

theorem wrle_def (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :
    `[fsl| wrle [program] ([[post]] | [[resource]])] = match program with
  | [Prog| ↓ ] => post
  | [Prog| ↯ ] => `[fsl| fFalse]
  | program => `[fsl| [[resource]] -⋆ [[step program
    (fun c => `[fsl| wrle [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [wrle', wrleStepHom, ← map_gfp, coe_mk, wrleStep]
  split
  case h_1 =>
    split
    case h_1 => rfl
    case h_2 h => cases h
    case h_3 => rfl
  case h_2 =>
    split
    case h_1 h => cases h
    case h_2 => rfl
    case h_3 => rfl
  case h_3 h_n_term h_n_err =>
    split
    case h_1 => exfalso; apply h_n_term; rfl
    case h_2 => exfalso; apply h_n_err; rfl
    case h_3 => rfl

theorem wrle_eq_of_not_final {program : Program Var} (h_not_final : ¬ finalProgram program)
    (post : StateRV Var) (resource : StateRV Var) : `[fsl| wrle [program] ([[post]] | [[resource]])]
    = `[fsl| [[resource]] -⋆ [[step program
      (fun c => `[fsl| wrle [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [finalPrograms_iff_or, not_or] at h_not_final
  obtain ⟨h_n_term, h_n_err⟩ := h_not_final
  rw [wrle_def]
  split
  case h_1 => simp only [not_true_eq_false] at h_n_term
  case h_2 => simp only [not_true_eq_false] at h_n_err
  case h_3 => rfl

theorem wrle_eq_of_term
    (post : StateRV Var) (resource : StateRV Var) :
    `[fsl| wrle [ [Prog| ↓] ] ([[post]] | [[resource]])] = post := by
  rw [wrle_def]

theorem wrle_eq_of_abort
    (post : StateRV Var) (resource : StateRV Var) :
    `[fsl| wrle [ [Prog| ↯] ] ([[post]] | [[resource]])] = `[fsl| fFalse] := by
  rw [wrle_def]


end CFSL
