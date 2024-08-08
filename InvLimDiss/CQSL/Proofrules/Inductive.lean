import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.CQSL.Proofrules.Auxiliary
import InvLimDiss.CQSL.Step.Framing
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

open State in
theorem wrle_concur {e : BoolExp Var}
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁) = ∅)
    (h_vars_resource₁ : varRV P₁ ∩ varRV resource = ∅)
    (h_vars_resource₂ : varRV P₂ ∩ varRV resource = ∅) :
    `[qsl| wrle [c₁] ([[P₁]] | [[resource]]) ⋆
           wrle [c₂] ([[P₂]] | [[resource]])
      ⊢ wrle [[[c₁]] || [[c₂]]] ([[P₁]] ⋆ [[P₂]] | [[resource]])] := by
  unfold wrle'
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  induction (Order.succ (Cardinal.mk _)).ord using Ordinal.induction generalizing c₁ c₂ with
  | h i ih =>
    intro s
    nth_rw 3 [gfpApprox]
    apply le_sInf
    simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · apply le_one'
    · simp only [wrle_step]
      apply le_sInf
      rintro _ ⟨heap', h_disjoint', rfl⟩
      cases eq_or_ne c₁ [Prog| ↯] with
      | inl h_c₁_abort =>
        rw [h_c₁_abort]
        apply sSup_le
        rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
        rw [← unit_le_div_iff_mul_le]
        rw [gfpApprox]
        apply sInf_le_of_le
        · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
            Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
            exists_exists_and_eq_and]
          use 0
          apply And.intro
          · apply Or.inr
            use i', h_i'
            simp only [wrle_step]
            rfl
          · rfl
        · exact nonneg'
      | inr h_c₁_neq_abort =>
        cases eq_or_ne c₂ [Prog| ↯] with
        | inl h_c₂_abort =>
          rw [h_c₂_abort]
          apply sSup_le
          rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
          rw [mul_comm, ← unit_le_div_iff_mul_le]
          rw [gfpApprox]
          apply sInf_le_of_le
          · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
              Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
              exists_exists_and_eq_and]
            use 0
            apply And.intro
            · apply Or.inr
              use i', h_i'
              simp only [wrle_step]
              rfl
            · rfl
          · exact nonneg'
        | inr h_c₂_neq_abort =>
          cases eq_or_ne c₁ [Prog| ↓] with
          | inl h_c₁_term =>
            rw [h_c₁_term]
            apply sSup_le
            rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
            rw [← unit_le_div_iff_mul_le]
            rw [gfpApprox]
            apply sInf_le_of_le
            · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
                Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
                exists_exists_and_eq_and]
              use P₁
              apply And.intro
              · apply Or.inr
                use i', h_i'
                simp only [wrle_step]
              · rfl
            · cases eq_or_ne c₂ [Prog| ↓] with
              | inl h_c₂_term =>
                rw [h_c₂_term]
                rw [unit_le_div_iff_mul_le, mul_comm, ← unit_le_div_iff_mul_le]
                rw [gfpApprox]
                apply sInf_le_of_le
                · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                    Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp,
                    Pi.top_apply, exists_exists_and_eq_and]
                  use P₂
                  apply And.intro
                  · apply Or.inr
                    use i', h_i'
                    simp only [wrle_step]
                  · rfl
                · rw [unit_le_div_iff_mul_le, unit_le_div_iff_mul_le]
                  rw [step_concurrent_term]
                  apply le_sSup_of_le
                  · use s.heap, heap', h_disjoint', rfl
                  · apply unit_mul_le_mul
                    · rw [mul_comm]
                      rw [gfpApprox]
                      apply le_sInf
                      simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                        Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp,
                        Pi.top_apply, exists_exists_and_eq_and, forall_exists_index, and_imp,
                        forall_apply_eq_imp_iff₂]
                      rintro _ (rfl | ⟨_, _, rfl⟩)
                      · exact le_one'
                      · simp only [wrle_step]
                        apply le_sSup
                        use heap₁, heap₂, h_disjoint, h_union
                    · rfl
              | inr h_c₂_neq_term =>
                rw [step_concurrent_cont_only_right _ _ h_c₂_neq_term h_c₂_neq_abort]
                rw [unit_le_div_iff_mul_le, mul_comm, ← unit_le_div_iff_mul_le]
                rw [gfpApprox]
                apply sInf_le_of_le
                · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                    Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp,
                    Pi.top_apply, exists_exists_and_eq_and]
                  use ?_
                  apply And.intro
                  · apply Or.inr
                    use i', h_i'
                    exact rfl
                  · rfl
                · simp only [wrle_step]
                  apply sInf_le_of_le
                  · use heap'
                    apply And.intro
                    · simp only
                      rw [← h_union, disjoint_comm _ _, disjoint_union_iff] at h_disjoint'
                      rw [disjoint_comm _ _]
                      exact h_disjoint'.right
                    · rfl
                  · rw [div_swap]
                    apply unit_div_le_div ?_ le_rfl
                    rw [unit_le_div_iff_mul_le]
                    apply le_trans
                    swap
                    · apply step_mono_of_semantics_support
                      intro s a h_a c' s' h_semantics
                      apply qslSepMul_mono ?_ le_rfl
                      swap
                      apply ih i' h_i'
                      · simp only [wrtProg, Set.empty_inter]
                      · apply Set.Subset.antisymm
                        · apply Set.Subset.trans
                          · exact Set.inter_subset_inter
                              (written_of_transition h_semantics)
                              (Set.Subset.rfl)
                          · rw [← h_c₁_term]
                            exact subset_of_eq h_vars₂
                        · exact Set.empty_subset _
                    · apply le_trans
                      swap
                      · apply step_mono
                        intro c' s'
                        simp only
                        apply qslSepMul_mono ?_ le_rfl
                        swap
                        apply qslSepMul_mono ?_ le_rfl
                        swap
                        unfold gfpApprox
                        apply le_sInf
                        simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                          Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
                          exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
                        rintro _ (rfl | ⟨_, _, rfl⟩)
                        · simp only [le_top]
                        · simp only [wrle_step]
                          exact le_rfl
                      · simp_rw [qslSepMul_comm P₁ _, ← qslSepMul_assoc, qslSepMul_comm P₁ _]
                        simp_rw [qslSepMul_assoc]
                        apply le_trans ?_ (step_framing _ ?_ ⟨s.stack, s.heap ∪ heap'⟩)
                        swap
                        · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
                          apply Set.Subset.trans ?_ (subset_of_eq h_vars₂)
                          exact Set.inter_subset_inter
                            wrtStmt_subset_wrtProg
                            Set.subset_union_right
                        · apply le_sSup
                          use heap₂ ∪ heap', heap₁
                          simp only [and_true]
                          have : disjoint heap₁ heap' := by {
                            rw [← h_union, disjoint_comm _ _, disjoint_union_iff] at h_disjoint'
                            rw [disjoint_comm _ _]
                            exact h_disjoint'.left
                          }
                          apply And.intro
                          · rw [disjoint_comm _ _, disjoint_union_iff]
                            use h_disjoint, this
                          · rw [← h_union]
                            rw [union_comm heap₁ heap₂ h_disjoint]
                            nth_rw 2 [union_assoc]
                            rw [union_comm heap₁ heap' this]
                            rw [← union_assoc]
          | inr h_c₁_neq_term =>
            cases eq_or_ne c₂ [Prog| ↓] with
            | inl h_c₂_term =>
              rw [h_c₂_term]
              apply sSup_le
              rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
              rw [mul_comm, ← unit_le_div_iff_mul_le]
              rw [gfpApprox]
              apply sInf_le_of_le
              · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
                  Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
                  exists_exists_and_eq_and]
                use P₂
                apply And.intro
                · apply Or.inr
                  use i', h_i'
                  simp only [wrle_step]
                · rfl
              rw [step_concurrent_cont_only_left _ _ h_c₁_neq_term h_c₁_neq_abort]
              rw [unit_le_div_iff_mul_le, mul_comm, ← unit_le_div_iff_mul_le]
              rw [gfpApprox]
              apply sInf_le_of_le
              · simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                  Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp,
                  Pi.top_apply, exists_exists_and_eq_and]
                use ?_
                apply And.intro
                · apply Or.inr
                  use i', h_i'
                  exact rfl
                · rfl
              · simp only [wrle_step]
                apply sInf_le_of_le
                · use heap'
                  apply And.intro
                  · simp only
                    rw [← h_union, disjoint_comm _ _, disjoint_union_iff] at h_disjoint'
                    rw [disjoint_comm _ _]
                    exact h_disjoint'.left
                  · rfl
                · rw [div_swap]
                  apply unit_div_le_div ?_ le_rfl
                  rw [unit_le_div_iff_mul_le]
                  apply le_trans
                  swap
                  · apply step_mono_of_semantics_support
                    intro s a h_a c' s' h_semantics
                    apply qslSepMul_mono ?_ le_rfl
                    swap
                    apply ih i' h_i'
                    · apply Set.Subset.antisymm
                      · apply Set.Subset.trans
                        · exact Set.inter_subset_inter
                            (written_of_transition h_semantics)
                            (Set.Subset.rfl)
                        · rw [← h_c₂_term]
                          exact subset_of_eq h_vars₁
                      · exact Set.empty_subset _
                    · simp only [wrtProg, Set.empty_inter]
                  · apply le_trans
                    swap
                    · apply step_mono
                      intro c' s'
                      simp only
                      apply qslSepMul_mono ?_ le_rfl
                      swap
                      apply qslSepMul_mono le_rfl ?_
                      swap
                      unfold gfpApprox
                      apply le_sInf
                      simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop,
                        Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
                        exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
                      rintro _ (rfl | ⟨_, _, rfl⟩)
                      · simp only [le_top]
                      · simp only [wrle_step]
                        exact le_rfl
                    · simp_rw [← qslSepMul_assoc, qslSepMul_comm P₂ _]
                      simp_rw [qslSepMul_assoc]
                      apply le_trans ?_ (step_framing _ ?_ ⟨s.stack, s.heap ∪ heap'⟩)
                      swap
                      · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
                        apply Set.Subset.trans ?_ (subset_of_eq h_vars₁)
                        exact Set.inter_subset_inter
                          wrtStmt_subset_wrtProg
                          Set.subset_union_right
                      · apply le_sSup
                        use heap₁ ∪ heap', heap₂
                        simp only [and_true]
                        have : disjoint heap₂ heap' := by {
                          rw [← h_union, disjoint_comm _ _, disjoint_union_iff] at h_disjoint'
                          rw [disjoint_comm _ _]
                          exact h_disjoint'.right
                        }
                        apply And.intro
                        · rw [disjoint_comm _ _, disjoint_union_iff]
                          rw [disjoint_comm heap₂ _]
                          use h_disjoint, this
                        · rw [← h_union]
                          nth_rw 2 [union_assoc]
                          rw [union_comm heap₂ heap' this]
                          rw [← union_assoc]
            | inr h_c₂_neq_term => sorry

end CQSL
