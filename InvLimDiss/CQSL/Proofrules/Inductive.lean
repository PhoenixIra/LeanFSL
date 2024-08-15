import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.CQSL.Proofrules.Auxiliary
import InvLimDiss.CQSL.Proofrules.VarRV
import InvLimDiss.CQSL.Step.Framing
import InvLimDiss.SL.QuantitativeSubstSimp
import InvLimDiss.Mathlib.FixedPoints

/-!
  Proofrules for wrle with inductive programs (i.e. concurrency and sequencing) as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics OrdinalApprox

variable {Vars : Type}

lemma gfpApprox_wrle_step_seq :
    gfpApprox
      (wrle_step_hom (gfpApprox (wrle_step_hom P resource) ⊤ k c₂) resource)
      ⊤ (Order.succ k) c₁
    ≤ gfpApprox (wrle_step_hom P resource) ⊤ k [Prog| [[c₁]] ; [[c₂]]] := by
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
    simp only [wrle_step_hom, wrle_step]
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
              change _ ≤ gfpApprox (wrle_step_hom P resource) ⊤ k' c₂ s
              exact (OrdinalApprox.gfpApprox_antitone
                  (wrle_step_hom _ _) _ (le_of_lt h_k')) c₂ s
      | inr h_ne_term₁ =>
        cases eq_or_ne c₁ [Prog| ↯] with
        | inl h_abort₁ =>
          rw [h_abort₁, step_sequential_abort _ _]
          rw [zero_unit_div_of_ne _ h_resource_neq_zero]
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
            Order.lt_succ_iff, exists_prop, exists_exists_and_eq_and]
          use k', le_of_lt h_k'
          simp only [coe_mk, wrle_step, qslFalse]
        | inr h_ne_abort₁ =>
          apply sInf_le_of_le
          · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
              Order.lt_succ_iff, exists_prop, exists_exists_and_eq_and]
            have : Order.succ k' ≤ k := by exact Order.succ_le_iff.mpr h_k'
            use Order.succ k', this
          · rw [step_sequential_cont _ _ h_ne_term₁ h_ne_abort₁]
            simp only [coe_mk, wrle_step]
            apply sInf_le_of_le
            · use heap', h_disjoint
            · apply unit_div_le_div ?_ le_rfl
              apply step_mono c₁
              intro c₁'
              simp only
              apply qslSepMul_mono ?_ le_rfl
              apply le_trans ?_ (ih k' h_k')
              apply OrdinalApprox.gfpApprox_le_gfpApprox_of_le
                (wrle_step_hom (gfpApprox (wrle_step_hom _ _) _ _ _) _)
              simp only [wrle_step_hom, mk_le_mk]
              apply wrle_step_mono_of_le_RV
              apply OrdinalApprox.gfpApprox_antitone
                (wrle_step_hom P resource) ⊤ (le_of_lt h_k')

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

private lemma gfpApprox_wrle_step_concur_symmetric_of_left_abort
    (c : Program Var) (P resource : StateRV Var) (i : Ordinal) :
    gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| ↯ || [[c]]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c]] || ↯]) := by
  unfold gfpApprox
  apply le_antisymm
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i', h_i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_abort_left]
        exact nonneg'
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_abort_right]
        exact nonneg'


private lemma gfpApprox_wrle_step_concur_symmetric_of_left_term
    {c : Program Var} (P resource : StateRV Var) (i : Ordinal)
    (h_neq_abort : c ≠ [Prog| ↯]) (h_neq_term : c ≠ [Prog| ↓])
    (h_ind : ∀ i' < i, ∀ c',
    gfpApprox (wrle_step_hom P resource) ⊤ i' ([Prog| ↓ || [[c']]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i' ([Prog| [[c']] || ↓])) :
    gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| ↓ || [[c]]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c]] || ↓]) := by
  unfold gfpApprox
  apply le_antisymm
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_cont_only_right _ _ h_neq_term h_neq_abort]
        rw [step_concurrent_cont_only_left _ _ h_neq_term h_neq_abort]
        apply step_mono
        intro c s
        simp only
        specialize h_ind i' h_i' c
        simp only [wrle_step_hom] at h_ind
        rw [h_ind]
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_cont_only_right _ _ h_neq_term h_neq_abort]
        rw [step_concurrent_cont_only_left _ _ h_neq_term h_neq_abort]
        apply step_mono
        intro c s
        simp only
        specialize h_ind i' h_i' c
        simp only [wrle_step_hom] at h_ind
        rw [h_ind]

private lemma gfpApprox_wrle_step_concur_symmetric_of_no_term
    {c₁ c₂ : Program Var} (P resource : StateRV Var) (i : Ordinal)
    (h_c₁_neq_abort : c₁ ≠ [Prog| ↯]) (h_c₁_neq_term : c₁ ≠ [Prog| ↓])
    (h_c₂_neq_abort : c₂ ≠ [Prog| ↯]) (h_c₂_neq_term : c₂ ≠ [Prog| ↓])
    (h_ind : ∀ i' < i, ∀ c₁' c₂',
    gfpApprox (wrle_step_hom P resource) ⊤ i' ([Prog| [[c₁']] || [[c₂']]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i' ([Prog| [[c₂']] || [[c₁']]])) :
    gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c₁]] || [[c₂]]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c₂]] || [[c₁]]]) := by
  unfold gfpApprox
  apply le_antisymm
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_cont _ _ h_c₂_neq_term h_c₁_neq_term h_c₂_neq_abort h_c₁_neq_abort]
        apply le_min
        · rw [step_concurrent_cont _ _ h_c₁_neq_term h_c₂_neq_term h_c₁_neq_abort h_c₂_neq_abort]
          apply min_le_of_right_le
          apply step_mono
          intro c' s'
          simp only
          specialize h_ind i' h_i' c₁ c'
          simp only [wrle_step_hom] at h_ind
          rw [h_ind]
        · rw [step_concurrent_cont _ _ h_c₁_neq_term h_c₂_neq_term h_c₁_neq_abort h_c₂_neq_abort]
          apply min_le_of_left_le
          apply step_mono
          intro c' s'
          simp only
          specialize h_ind i' h_i' c' c₂
          simp only [wrle_step_hom] at h_ind
          rw [h_ind]
  · apply le_sInf
    simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · intro s; exact le_one'
    · apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
        apply Or.inr
        use i'
      · simp only [wrle_step_hom, coe_mk, wrle_step]
        apply qslSepDiv_mono le_rfl
        intro s
        rw [step_concurrent_cont _ _ h_c₁_neq_term h_c₂_neq_term h_c₁_neq_abort h_c₂_neq_abort]
        apply le_min
        · rw [step_concurrent_cont _ _ h_c₂_neq_term h_c₁_neq_term h_c₂_neq_abort h_c₁_neq_abort]
          apply min_le_of_right_le
          apply step_mono
          intro c' s'
          simp only
          specialize h_ind i' h_i' c₂ c'
          simp only [wrle_step_hom] at h_ind
          rw [h_ind]
        · rw [step_concurrent_cont _ _ h_c₂_neq_term h_c₁_neq_term h_c₂_neq_abort h_c₁_neq_abort]
          apply min_le_of_left_le
          apply step_mono
          intro c' s'
          simp only
          specialize h_ind i' h_i' c' c₁
          simp only [wrle_step_hom] at h_ind
          rw [h_ind]

theorem gfpApprox_wrle_step_concur_symmetric
    (c₁ c₂ : Program Var) (P resource : StateRV Var) (i : Ordinal) :
    gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c₁]] || [[c₂]]])
    = gfpApprox (wrle_step_hom P resource) ⊤ i ([Prog| [[c₂]] || [[c₁]]]) := by
  induction i using Ordinal.induction generalizing c₁ c₂ with
  | h i ih =>
    cases eq_or_ne c₁ [Prog| ↯] with
    | inl h_c₁_abort =>
      rw [h_c₁_abort]
      exact gfpApprox_wrle_step_concur_symmetric_of_left_abort c₂ P resource i
    | inr h_c₁_neq_abort =>
      cases eq_or_ne c₂ [Prog| ↯] with
      | inl h_c₂_abort =>
        rw [h_c₂_abort, eq_comm]
        exact gfpApprox_wrle_step_concur_symmetric_of_left_abort c₁ P resource i
      | inr h_c₂_neq_abort =>
        cases eq_or_ne c₁ [Prog| ↓] with
        | inl h_c₁_term =>
          rw [h_c₁_term]
          cases eq_or_ne c₂ [Prog| ↓] with
          | inl h_c₂_term =>
            rw [h_c₂_term]
          | inr h_c₂_neq_term =>
            apply gfpApprox_wrle_step_concur_symmetric_of_left_term _ _ _
              h_c₂_neq_abort h_c₂_neq_term
            intro i' h_i' c'
            apply ih i' h_i'
        | inr h_c₁_neq_term =>
          cases eq_or_ne c₂ [Prog| ↓] with
          | inl h_c₂_term =>
            rw [h_c₂_term, eq_comm]
            apply gfpApprox_wrle_step_concur_symmetric_of_left_term _ _ _
              h_c₁_neq_abort h_c₁_neq_term
            intro i' h_i' c'
            apply ih i' h_i'
          | inr h_c₂_neq_term =>
            apply gfpApprox_wrle_step_concur_symmetric_of_no_term _ _ _
              h_c₁_neq_abort h_c₁_neq_term h_c₂_neq_abort h_c₂_neq_term
            intro i' h_i' c₁' c₂'
            apply ih i' h_i'

theorem wrle_concur_symmetric
    (c₁ c₂ : Program Var) (P resource : StateRV Var) :
    `[qsl| wrle [[[c₁]] || [[c₂]]] ([[P]] | [[resource]])]
    = `[qsl| wrle [[[c₂]] || [[c₁]]] ([[P]] | [[resource]])] := by
  unfold wrle'
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  exact gfpApprox_wrle_step_concur_symmetric c₁ c₂ P resource _


private lemma wrle_concur_of_left_abort
    (c : Program Var) (P₁ P₂ resource : StateRV Var) :
    (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ i [Prog| ↯ ] ]]
    ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ i c]] ]) ≤
    gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource) ⊤ i ([Prog| ↯ || [[c]]]) := by
  unfold gfpApprox
  apply le_sInf
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
  rintro _ (rfl | ⟨i', h_i', rfl⟩)
  · intro s; exact le_one'
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
    simp only [wrle_step_hom, coe_mk, wrle_step]
    apply le_sInf
    rintro _ ⟨heap', _, rfl⟩
    rw [← unit_le_div_iff_mul_le]
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

private lemma wrle_concur_of_term
    (P₁ P₂ resource : StateRV Var) :
    (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ i [Prog| ↓ ] ]]
    ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ i [Prog| ↓ ] ]] ]) ≤
    gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource) ⊤ i ([Prog| ↓ || ↓ ]) := by
  unfold gfpApprox
  apply le_sInf
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
  rintro _ (rfl | ⟨i', h_i', rfl⟩)
  · intro s; exact le_one'
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    simp only [wrle_step_hom, coe_mk, wrle_step]
    apply le_sInf
    rintro _ ⟨heap', h_disjoint', rfl⟩
    rw [step_concurrent_term _ _]
    rw [unit_le_div_iff_mul_le]
    apply le_sSup_of_le
    · use s.heap, heap'
    · apply unit_mul_le_mul ?_ le_rfl
      rw [gfpApprox]
      apply le_sInf
      simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
        Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
        exists_exists_and_eq_and, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro _ (rfl | ⟨_, _, rfl⟩)
      · exact le_one'
      · simp only [wrle_step]
        rw [← unit_le_div_iff_mul_le]
        apply sInf_le_of_le
        · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
            exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
          use P₁
          apply And.intro
          · apply Or.inr
            use i', h_i'
            simp only [wrle_step]
          · rfl
        · rw [unit_le_div_iff_mul_le, mul_comm, ← unit_le_div_iff_mul_le]
          apply sInf_le_of_le
          · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
              exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
            use P₂
            apply And.intro
            · apply Or.inr
              use i', h_i'
              simp only [wrle_step]
            · rfl
          · rw [unit_le_div_iff_mul_le, mul_comm]
            apply le_sSup
            use heap₁, heap₂

open State in
private lemma wrle_concur_cont_of_left_term
    {c : Program Var} {P₁ P₂ resource : StateRV Var}
    (h_neq_abort : c ≠ [Prog| ↯]) (h_neq_term : c ≠ [Prog| ↓])
    (h_vars  : wrtProg c ∩ (varRV P₁ ∪ varRV resource) = ∅)
    (h_ind : ∀ k < i, ∀ {c : Program Var},
      wrtProg c ∩ (varRV P₁ ∪ varRV resource) = ∅ →
        (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ k [Prog| ↓] ]]
        ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ k c]] ])
        ≤ gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource)
          ⊤ k ([Prog| ↓ || [[c]]])) :
    (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ i [Prog| ↓ ] ]]
    ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ i c]] ]) ≤
    gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource) ⊤ i ([Prog| ↓ || [[c]]]) := by
  unfold gfpApprox
  apply le_sInf
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
  rintro _ (rfl | ⟨i', h_i', rfl⟩)
  · intro s; exact le_one'
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    simp only [wrle_step_hom, coe_mk, wrle_step]
    apply le_sInf
    rintro _ ⟨heap', h_disjoint', rfl⟩
    rw [step_concurrent_cont_only_right _ _ h_neq_term h_neq_abort]
    rw [← unit_le_div_iff_mul_le]
    apply sInf_le_of_le
    · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq, exists_prop,
        exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
      use P₁
      apply And.intro
      · apply Or.inr
        use i', h_i'
        simp only [wrle_step]
      · rfl
    · rw [unit_le_div_iff_mul_le, mul_comm, ← unit_le_div_iff_mul_le]
      apply sInf_le_of_le
      · simp only [Set.mem_range, Subtype.exists, Set.mem_insert_iff, Set.mem_setOf_eq,
          exists_prop, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
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
            intro s a _ c' s' h_semantics
            apply qslSepMul_mono ?_ le_rfl
            swap
            apply h_ind i' h_i'
            apply Set.Subset.antisymm
            · apply Set.Subset.trans
              · exact Set.inter_subset_inter
                  (written_of_transition h_semantics)
                  (Set.Subset.rfl)
              · simp only [varProg, Set.empty_union, Set.subset_empty_iff]
                exact h_vars
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
              · intro s; exact le_one'
              · simp only [wrle_step_hom, coe_mk, wrle_step]
                exact le_rfl
            · simp_rw [qslSepMul_comm P₁ _, ← qslSepMul_assoc, qslSepMul_comm P₁ _]
              simp_rw [qslSepMul_assoc]
              apply le_trans ?_ (step_framing _ ?_ ⟨s.stack, s.heap ∪ heap'⟩)
              swap
              · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
                apply Set.Subset.trans ?_ (subset_of_eq h_vars)
                exact Set.inter_subset_inter
                  wrtStmt_subset_wrtProg
                  Set.subset_union_left
              · apply le_sSup
                use heap₂ ∪ heap', heap₁
                simp only [wrle_step_hom, and_true]
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

open State in
private lemma wrle_concur_cont_of_left
    {c₁ c₂ : Program Var} {P₁ P₂ resource : StateRV Var}
    {stack : Stack Var} {heap heap₁ heap₂ heap' : Heap}
    {i i' : Ordinal} (h_i' : i' < i)
    (h_disjoint : disjoint heap₁ heap₂) (h_union : heap₁ ∪ heap₂ = heap)
    (h_disjoint' : disjoint heap heap')
    (h_c₁_neq_abort : c₁ ≠ [Prog| ↯]) (h_c₁_neq_term : c₁ ≠ [Prog| ↓])
    (h_c₂_neq_abort : c₂ ≠ [Prog| ↯]) (h_c₂_neq_term : c₂ ≠ [Prog| ↓])
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV resource) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV resource) = ∅)
    (h_ind : ∀ k < i, ∀ {c₁ c₂ : Program Var},
      wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV resource) = ∅ →
      wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV resource) = ∅ →
        (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ k c₁]]
        ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ k c₂]] ])
        ≤ gfpApprox
          (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource)
          ⊤ k ([Prog| [[c₁]] || [[c₂]]])) :
      gfpApprox (wrle_step_hom P₁ resource) ⊤ i c₁ ⟨ stack, heap₁⟩
    * gfpApprox (wrle_step_hom P₂ resource) ⊤ i c₂ ⟨ stack, heap₂⟩
    * resource ⟨stack, heap'⟩
    ≤ step c₁ (fun c ↦
      `[qsl|
        [[gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource)
            ⊤ i' ([Prog| [[c]] || [[c₂]]])]]
          ⋆ [[resource]] ])
      ⟨ stack, heap ∪ heap' ⟩ := by
  rw [← unit_le_div_iff_mul_le, ← unit_le_div_iff_mul_le]
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
  · rw [wrle_step_hom, OrderHom.coe_mk, wrle_step]
    simp only
    rw [← h_union, disjoint_comm _ _, disjoint_union_iff] at h_disjoint'
    apply sInf_le_of_le
    · use heap'
      apply And.intro
      · simp only
        rw [disjoint_comm _ _]
        exact h_disjoint'.left
      · rfl
    · rw [div_swap]
      apply unit_div_le_div ?_ le_rfl
      rw [unit_le_div_iff_mul_le]
      apply le_trans
      swap
      · apply step_mono_of_state_of_semantics_support
        intro a _ c' s' h_semantics
        apply qslSepMul_mono ?_ le_rfl
        swap
        apply h_ind i' h_i'
        · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
          apply Set.Subset.trans ?_ (subset_of_eq h_vars₁)
          exact Set.inter_subset_inter
            (written_of_transition h_semantics)
            le_rfl
        · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
          apply Set.Subset.trans ?_ (subset_of_eq h_vars₂)
          apply Set.inter_subset_inter le_rfl
          apply Set.union_subset_union ?_ le_rfl
          apply Set.union_subset_union ?_ le_rfl
          exact vars_of_transition h_semantics
      · simp_rw [← qslSepMul_assoc, qslSepMul_comm _ _, qslSepMul_assoc]
        apply le_trans ?_ (step_framing _ ?_ ⟨stack, heap ∪ heap'⟩)
        swap
        · apply Set.Subset.antisymm ?_ (Set.empty_subset _)
          apply Set.Subset.trans ?_ (subset_of_eq h_vars₁)
          apply Set.inter_subset_inter wrtStmt_subset_wrtProg
          exact varRV_of_gfpApprox_wrle_step
        · apply le_sSup_of_le
          · use (heap₁ ∪ heap'), heap₂
            apply And.intro
            · rw [disjoint_comm _ _, disjoint_union_iff]
              rw [disjoint_comm heap₂ heap₁, disjoint_comm heap₂ heap']
              exact ⟨h_disjoint, h_disjoint'.right⟩
            · simp only [← h_union]
              rw [union_assoc, union_comm heap' heap₂ h_disjoint'.right]
              rw [← union_assoc]
              simp only [true_and]
              rfl
          · simp_rw [qslSepMul_comm]
            apply unit_mul_le_mul le_rfl
            apply OrdinalApprox.gfpApprox_antitone ⟨wrle_step P₂ resource,_⟩
            exact le_of_lt h_i'


open State in
private lemma wrle_concur_cont
    {c₁ c₂ : Program Var} {P₁ P₂ resource : StateRV Var}
    (h_c₁_neq_abort : c₁ ≠ [Prog| ↯]) (h_c₁_neq_term : c₁ ≠ [Prog| ↓])
    (h_c₂_neq_abort : c₂ ≠ [Prog| ↯]) (h_c₂_neq_term : c₂ ≠ [Prog| ↓])
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV resource) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV resource) = ∅)
    (h_ind : ∀ k < i, ∀ {c₁ c₂ : Program Var},
      wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV resource) = ∅ →
      wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV resource) = ∅ →
        (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ k c₁]]
        ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ k c₂]] ])
        ≤ gfpApprox
          (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource)
          ⊤ k ([Prog| [[c₁]] || [[c₂]]])) :
    (`[qsl| [[gfpApprox (wrle_step_hom P₁ resource) ⊤ i c₁ ]]
    ⋆ [[gfpApprox (wrle_step_hom P₂ resource) ⊤ i c₂]] ]) ≤
    gfpApprox (wrle_step_hom (`[qsl| [[P₁]] ⋆ [[P₂]] ]) resource) ⊤ i ([Prog| [[c₁]] || [[c₂]]]) := by
  nth_rw 3 [gfpApprox]
  apply le_sInf
  simp only [Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton, Set.mem_insert_iff,
    Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply, exists_exists_and_eq_and]
  rintro _ (rfl | ⟨i', h_i', rfl⟩)
  · intro s; exact le_one'
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    apply le_sInf
    rintro _ ⟨heap', h_disjoint', rfl⟩
    rw [step_concurrent_cont _ _
      h_c₁_neq_term h_c₂_neq_term
      h_c₁_neq_abort h_c₂_neq_abort]
    rw [unit_le_div_iff_mul_le]
    apply le_min
    · apply wrle_concur_cont_of_left h_i' h_disjoint h_union h_disjoint'
        h_c₁_neq_abort h_c₁_neq_term h_c₂_neq_abort h_c₂_neq_term
        h_vars₁ h_vars₂ h_ind
    · nth_rw 2 [mul_comm]
      rw [qslSepMul_comm]
      conv => right; left; intro c'; rw [gfpApprox_wrle_step_concur_symmetric]
      rw [union_comm _ _ h_disjoint] at h_union
      rw [disjoint_comm _ _] at h_disjoint
      apply wrle_concur_cont_of_left h_i' h_disjoint h_union h_disjoint'
        h_c₂_neq_abort h_c₂_neq_term h_c₁_neq_abort h_c₁_neq_term
        h_vars₂ h_vars₁
      intro i'' h_i'' c₁' c₂' h_vars₁' h_vars₂'
      rw [gfpApprox_wrle_step_concur_symmetric]
      rw [qslSepMul_comm]
      simp_rw [qslSepMul_comm]
      apply h_ind i'' h_i'' h_vars₂' h_vars₁'

open State in
theorem wrle_concur
    {c₁ c₂ : Program Vars} {P₁ P₂ resource : StateRV Vars}
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV resource) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV resource) = ∅) :
    `[qsl| wrle [c₁] ([[P₁]] | [[resource]]) ⋆
           wrle [c₂] ([[P₂]] | [[resource]])
      ⊢ wrle [[[c₁]] || [[c₂]]] ([[P₁]] ⋆ [[P₂]] | [[resource]])] := by
  unfold wrle'
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  induction (Order.succ (Cardinal.mk _)).ord using Ordinal.induction generalizing c₁ c₂ with
  | h i ih =>
    cases eq_or_ne c₁ [Prog| ↯] with
    | inl h_c₁_abort =>
      rw [h_c₁_abort]
      apply wrle_concur_of_left_abort
    | inr h_c₁_neq_abort =>
      cases eq_or_ne c₂ [Prog| ↯] with
      | inl h_c₂_abort =>
        rw [h_c₂_abort]
        rw [gfpApprox_wrle_step_concur_symmetric]
        rw [qslSepMul_comm]
        simp_rw [qslSepMul_comm P₁ P₂]
        apply wrle_concur_of_left_abort
      | inr h_c₂_neq_abort =>
        cases eq_or_ne c₁ [Prog| ↓] with
        | inl h_c₁_term =>
          rw [h_c₁_term]
          cases eq_or_ne c₂ [Prog| ↓] with
          | inl h_c₂_term =>
            rw [h_c₂_term]
            apply wrle_concur_of_term
          | inr h_c₂_neq_term =>
            simp only [h_c₁_term, varProg, Set.empty_union] at h_vars₂
            apply wrle_concur_cont_of_left_term h_c₂_neq_abort h_c₂_neq_term h_vars₂
            intro i' h_i' c h_vars
            apply ih i' h_i'
            · simp only [wrtProg, Set.empty_inter]
            · simp only [varProg, Set.empty_union]
              exact h_vars
        | inr h_c₁_neq_term =>
          cases eq_or_ne c₂ [Prog| ↓] with
          | inl h_c₂_term =>
            rw [h_c₂_term]
            rw [gfpApprox_wrle_step_concur_symmetric]
            rw [qslSepMul_comm]
            simp_rw [qslSepMul_comm P₁ P₂]
            simp only [h_c₂_term, varProg, Set.empty_union] at h_vars₁
            apply wrle_concur_cont_of_left_term h_c₁_neq_abort h_c₁_neq_term h_vars₁
            intro i' h_i' c h_vars
            rw [gfpApprox_wrle_step_concur_symmetric]
            rw [qslSepMul_comm]
            simp_rw [qslSepMul_comm P₂ P₁]
            apply ih i' h_i'
            · simp only [varProg, Set.empty_union]
              exact h_vars
            · simp only [wrtProg, Set.empty_inter]
          | inr h_c₂_neq_term =>
            apply wrle_concur_cont
              h_c₁_neq_abort h_c₁_neq_term h_c₂_neq_abort h_c₂_neq_term
              h_vars₁ h_vars₂ ih

end CQSL
