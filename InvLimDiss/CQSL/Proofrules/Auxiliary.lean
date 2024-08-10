import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.Mathlib.FixedPoints


namespace CQSL

open Syntax QSL

variable {Var : Type} {P Q : StateRV Var}

theorem wrle_step_mono_of_parameters_of_le_RV (h_le : P s ≤ Q s) :
    wrle_step P resource X c s ≤ wrle_step Q resource X c s := by
  simp only [wrle_step]
  split
  case h_1 => exact h_le
  case h_2 => rfl
  case h_3 => rfl

theorem wrle_step_mono_of_le_RV (h_le : P ≤ Q) :
    wrle_step P resource ≤ wrle_step Q resource := by
  intro X c s
  apply wrle_step_mono_of_parameters_of_le_RV
  exact h_le s

theorem wrle_mono (h : P ≤ Q) :
    `[qsl| wrle [c] ([[P]]|[[resource]]) ⊢ wrle [c] ([[Q]]|[[resource]])] := by
  intro s
  simp only [wrle']
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  apply OrdinalApprox.gfpApprox_le_gfpApprox_of_le
    (wrle_step_hom P resource) _ ?_ ⊤ (Order.succ (Cardinal.mk _)).ord _ _
  simp only [wrle_step_hom, OrderHom.mk_le_mk]
  exact wrle_step_mono_of_le_RV h



end CQSL
