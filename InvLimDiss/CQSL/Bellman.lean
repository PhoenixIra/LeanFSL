import InvLimDiss.CQSL.Step
import InvLimDiss.CQSL.WeakExpectation

/-! This file contains the equviality theorem for the bellman-solution and the concurrent
bellman-solution.

`wrle_of_emp_eq_bellman` states this equality. -/

namespace Bellman

open QSL Syntax OrderHom unitInterval Atom Semantics CQSL

variable {Var : Type}

/-- The bellman-operator.-/
noncomputable def bellman_step (post : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[qsl| qFalse]
  | X, program => `[qsl| [[step program (fun c => `[qsl| [[X c]]]) ]] ]

theorem bellman_monotone (post : StateRV Var) : Monotone (bellman_step post) := by
  intro X X' h_X
  unfold bellman_step
  rw [Pi.le_def]
  intro c
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply monotone_step c
    rw [Pi.le_def] at h_X ⊢
    intro c'
    exact h_X c'

/-- greatest solution of the bellman equation -/
noncomputable def bellman_solution (post : StateRV Var) : (Program Var → StateRV Var) :=
    gfp (⟨bellman_step post, bellman_monotone post⟩)

open OrderHom

theorem wrle_step_of_emp_eq_bellman {post : StateRV Var} :
    wrle_step post `[qsl| emp] = bellman_step post := by
  apply funext
  intro X
  apply funext
  intro c
  rw [wrle_step, bellman_step]
  split
  case h_1 => simp only
  case h_2 => simp only
  case h_3 =>
    simp only
    conv => left; rw [qslEmp_qslSepDiv_eq]; intro s; left; intro c; rw [qslSepMul_qslEmp_eq]

theorem gfp_wrle_eq_gfp_bellman {post : StateRV Var} :
    gfp (⟨wrle_step post `[qsl|emp], wrle_monotone post `[qsl| emp]⟩)
    = gfp (⟨bellman_step post, bellman_monotone post⟩) := by
  apply le_antisymm
  · apply le_gfp
    apply gfp_le
    intro X h_X
    apply le_trans h_X
    simp only [coe_mk]
    conv => left; intro c s; rw [wrle_step_of_emp_eq_bellman]
    apply bellman_monotone
    apply le_gfp
    exact h_X
  · apply le_gfp
    apply gfp_le
    intro X h_X
    apply le_trans h_X
    simp only [coe_mk]
    conv => left; intro c s; rw [← wrle_step_of_emp_eq_bellman]
    apply wrle_monotone
    apply le_gfp
    exact h_X

theorem wrle_of_emp_eq_bellman {c : Program Var} {post : StateRV Var} :
    `[qsl| wrle [c] ([[post]] | emp)] = bellman_solution post c := by
  unfold wrle' bellman_solution
  apply congrFun
  exact gfp_wrle_eq_gfp_bellman

end Bellman
