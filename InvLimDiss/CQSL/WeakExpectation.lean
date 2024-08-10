import InvLimDiss.CQSL.Step
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.AtomicFinal
import Mathlib.Order.FixedPoints

/-! This file contains the concurrent bellman-fixpoint and lemmas about, especially
  * `wrle_step` the concurrent bellman-operator
  * `wrle_step_mono` the concurrent bellman-operator is monotone
  * `wrle'` the fixpoint of the concurrent bellman-equation
  * `wrle_def` one unfolding of the bellman-solution

  We also offer syntax as `wrle` in the qsl environment. -/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics

variable {Var : Type}

/-- The concurrent bellman-operator.-/
noncomputable def wrle_step (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[qsl| qFalse]
  | X, program => `[qsl| [[resource]] -⋆ [[step program (fun c => `[qsl| [[X c]] ⋆ [[resource]] ]) ]] ]

theorem wrle_step_mono (post : StateRV Var) (resource : StateRV Var) : Monotone (wrle_step post resource) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro c
  unfold wrle_step
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply qslSepDiv_mono le_rfl
    apply step_mono
    rw [Pi.le_def]
    intro c
    rw [Pi.le_def]
    intro s
    apply qslSepMul_mono
    · rw [Pi.le_def] at h_X
      exact h_X c
    · exact le_rfl

/-- wrle_step as a monotone function -/
noncomputable def wrle_step_hom (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) →o (Program Var → StateRV Var) :=
  ⟨wrle_step post resource, wrle_step_mono post resource⟩

/-- The greatest solution to the concurrent bellman equation -/
noncomputable def wrle' (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :=
  gfp (wrle_step_hom post resource) program

syntax "wrle [" term "] (" qsl " | " qsl ")" : qsl
macro_rules
  | `(term| `[qsl| wrle [$c:term] ($p:qsl | $r:qsl)]) => `(wrle' $c `[qsl| $p] `[qsl| $r])
  | `(term| `[qsl $v| wrle [$c:term] ($p:qsl | $r:qsl)]) => `(wrle' $c `[qsl $v| $p] `[qsl $v| $r])


syntax "wrle [" program "] (" qsl " | " qsl ")" : qsl
macro_rules
  | `(term| `[qsl| wrle [$c:program] ($p:qsl | $r:qsl)]) =>
    `(wrle' [Prog| $c] `[qsl| $p] `[qsl| $r])
  | `(term| `[qsl $v| wrle [$c:program] ($p:qsl | $r:qsl)]) =>
    `(wrle' [Prog| $c] `[qsl $v| $p] `[qsl $v| $r])

open Lean PrettyPrinter Delaborator

def makeBrackets [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander wrle']
def unexpanderwrle : Unexpander
  | `($_ [Prog| $c:program] $p $r) =>
      do `(`[qsl| wrle [$c:program] ($(← makeBrackets p):qsl | $(← makeBrackets r):qsl )])
  | `($_ $c:term $p $r) =>
      do `(`[qsl| wrle [$c:term] ($(← makeBrackets p):qsl | $(← makeBrackets r):qsl )])
  | _ => throw ()

theorem wrle_def (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrle [program] ([[post]] | [[resource]])] = match program with
  | [Prog| ↓ ] => post
  | [Prog| ↯ ] => `[qsl| qFalse]
  | program => `[qsl| [[resource]] -⋆ [[step program
    (fun c => `[qsl| wrle [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [wrle', wrle_step_hom, ← map_gfp, coe_mk, wrle_step]
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
    (post : StateRV Var) (resource : StateRV Var) : `[qsl| wrle [program] ([[post]] | [[resource]])]
    = `[qsl| [[resource]] -⋆ [[step program
      (fun c => `[qsl| wrle [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [finalPrograms_iff_or, not_or] at h_not_final
  obtain ⟨h_n_term, h_n_err⟩ := h_not_final
  rw [wrle_def]
  split
  case h_1 => simp only [not_true_eq_false] at h_n_term
  case h_2 => simp only [not_true_eq_false] at h_n_err
  case h_3 => rfl

theorem wrle_eq_of_term
    (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrle [ [Prog| ↓] ] ([[post]] | [[resource]])] = post := by
  rw [wrle_def]

theorem wrle_eq_of_abort
    (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrle [ [Prog| ↯] ] ([[post]] | [[resource]])] = `[qsl| qFalse] := by
  rw [wrle_def]


end CQSL
