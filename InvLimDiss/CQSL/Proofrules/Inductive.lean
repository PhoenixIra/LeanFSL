import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.SL.Framing.Simps
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-!
  Proofrules for wrle with inductive programs (i.e. concurrency and sequencing) as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics OrdinalApprox

variable {Vars : Type}

theorem wrle_seq {P resource : StateRV Vars} {e : BoolExp Vars} :
    `[qsl| wrle [c₁] (wrle [c₂] ([[P]] | [[resource]]) | [[resource]])
      ⊢ wrle [[[c₁]] ; [[c₂]]] ([[P]] | [[resource]])] := by
  unfold wrle'
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_eq_of_mem_fixedPoints]
  case b => exact Order.succ (Order.succ (Cardinal.mk (Program Vars → StateRV Vars))).ord
  case h_init => exact le_top
  case h_ab => exact Order.le_succ _
  case h =>
    apply OrdinalApprox.gfpApprox_ord_mem_fixedPoint
    exact le_top
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  induction (Order.succ <| Cardinal.mk <| Program Vars → StateRV Vars).ord
    using Ordinal.induction generalizing c₁ with
  | h k ih =>
    intro s
    unfold gfpApprox
    simp only [coe_mk, exists_prop, Set.union_singleton, sInf_insert, Pi.inf_apply, Pi.top_apply,
      ge_iff_le, le_top, inf_of_le_right]
    apply le_sInf
    intro i h_i
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
      exists_exists_and_eq_and] at h_i
    obtain ⟨k', h_k', rfl⟩ := h_i
    simp only [wrle_step]
    apply le_sInf
    rintro _ ⟨heap', h_disjoint, rfl⟩
    cases eq_or_ne (resource ⟨s.stack, heap'⟩) 0 with
    | inl h_resource_zero =>
      simp only [h_resource_zero, unit_div_zero]
      exact le_one'
    | inr h_resource_neq_zero =>
      cases eq_or_ne c₁ [Prog| ↓] with
      | inl h_term₁ =>
        rw [h_term₁]
        rw [step_sequential_term _ _]
        split
        case isTrue h_abort₂ =>
          rw [zero_unit_div_of_ne _ h_resource_neq_zero]
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
            exists_exists_and_eq_and]
          use Order.succ k', Order.succ_lt_succ h_k'
          simp only [h_abort₂, wrle_step]
          sorry
        case isFalse => sorry
      | inr => sorry

theorem wrle_concur {e : BoolExp Var}
    (h_vars_res₁  : wrtProg c₁ ∩ varRV resource = ∅)
    (h_vars_prog₁ : wrtProg c₁ ∩ varRV P₂ = ∅)
    (h_vars_res₂  : wrtProg c₂ ∩ varRV resource = ∅)
    (h_vars_prog₂ : wrtProg c₂ ∩ varRV P₁ = ∅)
    (h_vars_prog  : wrtProg c₁ ∩ wrtProg c₂ = ∅) :
    `[qsl| wrle [c₁] ([[P₁]] | [[resource]]) ⋆
           wrle [c₂] ([[P₂]] | [[resource]])
      ⊢ wrle [[[c₁]] || [[c₂]]] ([[P₁]] ⋆ [[P₂]] | [[resource]])] := by
  sorry

end CQSL
