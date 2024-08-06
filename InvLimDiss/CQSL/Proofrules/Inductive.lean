import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.CQSL.Proofrules.Auxiliary
import InvLimDiss.SL.Framing.Simps
import InvLimDiss.Mathlib.FixedPoints

/-!
  Proofrules for wrle with inductive programs (i.e. concurrency and sequencing) as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics OrdinalApprox

variable {Vars : Type}

lemma gfpApprox_wrle_step_seq :
    gfpApprox ⟨wrle_step
      (gfpApprox ⟨wrle_step P resource, wrle_step_mono _ _⟩ ⊤ k c₂) resource, wrle_step_mono _ _⟩ ⊤ (Order.succ k) c₁
    ≤ gfpApprox ⟨wrle_step P resource, wrle_step_mono _ _⟩ ⊤ k [Prog| [[c₁]] ; [[c₂]]] := by
  induction k
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
          unfold gfpApprox
          apply le_antisymm ?_ nonneg'
          apply sInf_le
          simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
            Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
            exists_exists_and_eq_and]
          use 0
          apply And.intro ?_ (rfl)
          apply Or.inr
          use k', h_k'
          apply funext
          simp only [wrle_step, qslFalse, Pi.zero_apply, implies_true]
        case isFalse h_ne_abort₂ =>
          apply sInf_le_of_le
          · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
              Order.lt_succ_iff, exists_prop, exists_exists_and_eq_and]
            use k', le_of_lt h_k'
          · rw [unit_le_div_iff_mul_le]
            apply le_sSup_of_le
            · use s.heap, heap'
            · rw [← unit_le_div_iff_mul_le, unitInterval.mul_div_cancel h_resource_neq_zero]
              simp only [wrle_step]
              change _ ≤ gfpApprox ⟨wrle_step P resource, _⟩ ⊤ k' c₂ s
              have := (OrdinalApprox.gfpApprox_antitone ⟨wrle_step P resource, ?_⟩ ⊤ (le_of_lt h_k'))
              pick_goal 2
              · exact wrle_step_mono P resource
              · exact this c₂ s
      | inr h_ne_term₁ =>
        cases eq_or_ne c₁ [Prog| ↯] with
        | inl h_abort₁ =>
          rw [h_abort₁, step_sequential_abort _ _]
          rw [zero_unit_div_of_ne _ h_resource_neq_zero]
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
            Order.lt_succ_iff, exists_prop, exists_exists_and_eq_and]
          use k', le_of_lt h_k'
          simp only [wrle_step, qslFalse]
        | inr h_ne_abort₁ =>
          apply sInf_le_of_le
          · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
              Order.lt_succ_iff, exists_prop, exists_exists_and_eq_and]
            have : Order.succ k' ≤ k := by exact Order.succ_le_iff.mpr h_k'
            use Order.succ k', this
          · rw [step_sequential_cont _ _ h_ne_term₁ h_ne_abort₁]
            simp only [wrle_step]
            apply sInf_le_of_le
            · use heap', h_disjoint
            · apply unit_div_le_div ?_ le_rfl
              apply step_mono c₁
              intro c₁'
              simp only
              apply qslSepMul_mono ?_ le_rfl
              apply le_trans ?_ (ih k' h_k')
              apply OrdinalApprox.gfpApprox_le_gfpApprox_of_le
                ⟨wrle_step (gfpApprox ⟨wrle_step _ _, _⟩ _ _ _) _, _⟩
              simp only [mk_le_mk]
              apply wrle_step_mono_of_le_RV
              apply OrdinalApprox.gfpApprox_antitone ⟨wrle_step P resource, _⟩ ⊤ (le_of_lt h_k')

theorem wrle_seq {P resource : StateRV Vars} :
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
  exact gfpApprox_wrle_step_seq

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
