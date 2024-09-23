import InvLimDiss.CFSL.WeakExpectation
import InvLimDiss.CFSL.Step.Weighted
import InvLimDiss.Mathlib.FixedPoints


namespace CFSL

open Syntax FSL OrdinalApprox unitInterval

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
    `[fsl| wrle [c] ([[P]]|[[resource]]) ⊢ wrle [c] ([[Q]]|[[resource]])] := by
  intro s
  simp only [wrle']
  rw [← gfpApprox_ord_eq_gfp]
  rw [← gfpApprox_ord_eq_gfp]
  apply gfpApprox_le_gfpApprox_of_le
    (wrle_step_hom P resource) _ ?_ ⊤ (Order.succ (Cardinal.mk _)).ord _ _
  simp only [wrle_step_hom, OrderHom.mk_le_mk]
  exact wrle_step_mono_of_le_RV h

open State in
theorem wrle_share
    (h : `[fsl| [[Q]] ⊢ wrle [c] ([[P]]|[[resource₁]] ⋆ [[resource₂]])]) :
    `[fsl| [[Q]] ⋆ [[resource₂]] ⊢ wrle [c] ([[P]] ⋆ [[resource₂]]|[[resource₁]])] := by
  rw [← le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans h
  simp only [wrle']
  rw [← gfpApprox_ord_eq_gfp]
  rw [← gfpApprox_ord_eq_gfp]
  clear h
  induction (Order.succ (Cardinal.mk (Program Var → StateRV Var))).ord
    using Ordinal.induction generalizing c with
  | h i ih =>
    unfold gfpApprox
    intro s
    apply le_sInf
    rintro _ ⟨heap₂, h_disjoint₂, rfl⟩
    rw [unit_le_div_iff_mul_le]
    apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro _ (rfl|⟨j, h_j, rfl⟩)
    · exact le_one'
    · rw [← unit_le_div_iff_mul_le]
      apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        use ?_
        apply And.intro
        · right
          use j, h_j
          exact rfl
        · exact rfl
      · simp only [wrle_step_hom, OrderHom.coe_mk]
        cases eq_or_ne c [Prog| ↓]
        case inl h_term =>
          rw [h_term]
          simp only [wrle_step]
          rw [unit_le_div_iff_mul_le]
          apply le_sSup
          use s.heap, heap₂
        case inr h_n_term =>
          cases eq_or_ne c [Prog| ↯]
          case inl h_abort =>
            rw [h_abort]
            simp only [wrle_step, fslFalse, zero_le]
          case inr h_ne_abort =>
            simp only [wrle_step]
            rw [unit_le_div_iff_mul_le]
            apply le_sInf
            rintro _ ⟨heap₁, h_disjoint₁, rfl⟩
            rw [disjoint_comm, disjoint_union_iff, disjoint_comm] at h_disjoint₁
            rw [← unit_le_div_iff_mul_le]
            apply sInf_le_of_le
            · use (heap₁ ∪ heap₂)
              apply And.intro
              · rw [disjoint_union_iff]
                use h_disjoint₁.left, h_disjoint₂
              · exact rfl
            · rw [← div_mul_eq_div_div]
              apply unit_div_le_div
              swap
              · apply le_sSup
                use heap₁, heap₂, h_disjoint₁.right
              · simp only
                rw [union_assoc, union_comm heap₂ heap₁]
                swap
                · rw [disjoint_comm]
                  exact h_disjoint₁.right
                · apply step_mono
                  intro c
                  simp only
                  rw [fslSepMul_comm resource₁ resource₂, fslSepMul_assoc]
                  apply fslSepMul_mono ?_ le_rfl
                  simp only [Entailment.entail]
                  rw [← le_fslSepDiv_iff_fslSepMul_le, fslSepMul_comm resource₂ resource₁]
                  unfold wrle_step_hom at ih
                  exact ih j h_j

private theorem wrle_max_left :
    `[fsl| wrle [c] ([[P]] |[[R]]) ⊢ wrle [c] ([[P]] ⊔ [[Q]]|[[R]])] := by
  simp only [wrle', wrle_step_hom]
  rw [← gfpApprox_ord_eq_gfp]
  rw [← gfpApprox_ord_eq_gfp]
  induction (Order.succ (Cardinal.mk (Program Var → StateRV Var))).ord
    using Ordinal.induction generalizing c with
  | h i ih =>
    unfold gfpApprox
    apply le_sInf
    simp only [OrderHom.coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and]
    rintro _ (rfl|⟨j, h_j, rfl⟩)
    · intro s
      exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        right
        use j, h_j
      · cases eq_or_ne c [Prog| ↓]
        case inl h_term =>
          rw [h_term]
          simp only [wrle_step]
          intro s
          exact le_sup_left
        case inr h_n_term =>
          cases eq_or_ne c [Prog| ↯]
          case inl h_abort =>
            rw [h_abort]
            simp only [wrle_step, le_refl]
          case inr h_n_abort =>
            simp only [wrle_step]
            apply fslSepDiv_mono le_rfl
            apply step_mono
            intro c; simp only
            apply fslSepMul_mono ?_ le_rfl
            exact ih j h_j

theorem wrle_max :
    `[fsl| wrle [c] ([[P]] | [[R]]) ⊔ wrle [c] ([[Q]]|[[R]]) ⊢ wrle [c] ([[P]] ⊔ [[Q]]|[[R]])] := by
  apply sup_le
  · exact wrle_max_left
  · rw [fslMax_comm P Q]
    exact wrle_max_left

theorem wrle_weighted_sum (h : precise R) (h_vars : (wrtProg c) ∩ (varRV (fslReal e)) = ∅):
    `[fsl| <e> ⬝ wrle [c] ([[P]] | [[R]]) + ~<e> ⬝ wrle [c] ([[Q]] | [[R]])
    ⊢ wrle [c] (<e> ⬝ [[P]] + ~<e> ⬝ [[Q]]| [[R]])] := by
  simp only [wrle', wrle_step_hom]
  rw [← gfpApprox_ord_eq_gfp]
  rw [← gfpApprox_ord_eq_gfp]
  rw [← gfpApprox_ord_eq_gfp]
  induction (Order.succ (Cardinal.mk (Program Var → StateRV Var))).ord
    using Ordinal.induction generalizing c with
  | h i ih =>
    unfold gfpApprox
    apply le_sInf
    simp only [OrderHom.coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and]
    rintro _ (rfl|⟨j, h_j, rfl⟩)
    · exact le_top
    · rw [wrle_step]
      split
      case h_1 =>
        apply fslAdd_mono
        · apply fslMul_mono
          · exact le_rfl
          · apply sInf_le
            simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
              exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and, wrle_step,
              and_true]
            right; use j
        · apply fslMul_mono
          · exact le_rfl
          · apply sInf_le
            simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
              exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and, wrle_step,
              and_true]
            right; use j
      case h_2 =>
        conv => right; rw [← fslAdd_fslFalse fslFalse]
        apply fslAdd_mono
        · conv => right; rw [← fslMul_fslFalse (fslReal e)]
          apply fslMul_mono
          · exact le_rfl
          · apply sInf_le
            simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
              exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and, wrle_step,
              and_true]
            right; use j
        · conv => right; rw [← fslMul_fslFalse (fslNot <| fslReal e)]
          apply fslMul_mono
          · exact le_rfl
          · apply sInf_le
            simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
              exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and, wrle_step,
              and_true]
            right; use j
      case h_3 c _ _ _ _ =>
        rw [le_fslSepDiv_iff_fslSepMul_le]
        apply le_trans
        swap
        · apply step_mono_of_semantics_support
          intro s a _ c' s' h_semantics
          have h_vars' : wrtProg c' ∩ varRV (fslReal e) = ∅ := by {
              apply Set.Subset.antisymm
              · apply Set.Subset.trans
                · exact Set.inter_subset_inter (written_of_transition h_semantics) (Set.Subset.rfl)
                · exact subset_of_eq h_vars
              · exact Set.empty_subset _
            }
          apply le_trans ?_ (fslSepMul_mono (ih j h_j h_vars') le_rfl)
          swap
          rw [fslSepMul_comm, fslSepMul_weight_fslAdd_distr_of_precise _ _ _ _ h]
        · have h_stmt : wrtStmt c ∩ varRV (fslReal e) = ∅ := wrtStmt_inter_varRV_eq_emptyset_of_wrtProg h_vars
          apply le_trans ?_ (weighted_step_fslAdd_superdistr _ _ _ h_stmt)
          rw [← le_fslSepDiv_iff_fslSepMul_le]
          apply le_trans ?_ (fslSepdiv_weight_fslAdd_subdistr _ _ _)
          apply fslAdd_mono
          · apply fslMul_mono le_rfl
            apply sInf_le_of_le
            · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
                exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
              right
              use j, h_j
            · simp only [wrle_step]
              simp_rw [fslSepMul_comm]
              rfl
          · apply fslMul_mono le_rfl
            apply sInf_le_of_le
            · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
                exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
              right
              use j, h_j
            · simp only [wrle_step]
              simp_rw [fslSepMul_comm]
              rfl



end CFSL
