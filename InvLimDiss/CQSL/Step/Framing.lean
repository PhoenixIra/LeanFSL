import InvLimDiss.CQSL.Step.Atomic
import InvLimDiss.CQSL.Step.Flow
import InvLimDiss.CQSL.Step.Sequential
import InvLimDiss.CQSL.Step.Concurrent
import InvLimDiss.SL.Framing.Basic

namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical


theorem step_qslSepMul_eq_qslSepMul_step (h : (writtenVarProgram c) ∩ (varStateRV P) = ∅)
    (h_abort : inner [Prog| ↯] = `[qsl| qFalse]):
    `[qsl| [[step c inner]] ⋆ [[P]]] ⊢ step c (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  induction c generalizing inner with
  | terminated => rw [step_terminated, step_terminated]; exact le_one'
  | error => rw [step_error, step_error]; exact le_one'
  | skip' =>
    rw [step_skip, step_skip]
    apply le_sSup
    use heap₁, heap₂
  | assign v e =>
    rw [step_assign, step_assign]
    apply le_sSup_of_le
    use heap₁, heap₂, h_disjoint, h_union
    rw [Subtype.mk_le_mk]
    simp only [substituteStack, Set.Icc.coe_mul]
    cases eq_or_ne (inner [Prog| ↓] ⟨substituteVar s.stack v (e s.stack), heap₁⟩) 0 with
    | inl h_eq => rw [h_eq]; simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_ne =>
      rw [mul_le_mul_left]
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        rw [substituteVar_eq_of_not_varStateRV h (e s.stack)]
      · rw [ne_eq, Subtype.mk_eq_mk] at h_ne
        exact lt_of_le_of_ne nonneg' (Ne.symm h_ne)
  | manipulate e_loc e_val =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      rw [step_manipulate ⟨s.stack, heap₁⟩ _ h_l h_alloc]
      have h_heap : s.heap l ≠ undef := by
        rw [← h_union]; exact ne_undef_of_union_of_ne_undef h_alloc
      rw [step_manipulate s _ h_l h_heap]
      simp only [substituteHeap, ge_iff_le]
      apply le_sSup_of_le
      · use (substituteLoc heap₁ l (e_val s.stack)), heap₂
        rw [substituteLoc_disjoint h_alloc]
        use h_disjoint
        rw [← h_union]
        use substituteLoc_union
      · exact le_rfl
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_manipulate_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | lookup v e_loc =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      rw [undef_iff_exists_val] at h_alloc
      obtain ⟨q, h_alloc⟩ := h_alloc
      rw [step_lookup ⟨s.stack, heap₁⟩ _ h_l h_alloc]
      have h_heap : s.heap l = q := by
        rw [← h_union]; exact union_val_of_val h_alloc
      rw [step_lookup s _ h_l h_heap]
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        simp only [substituteStack]
        rw [substituteVar_eq_of_not_varStateRV h q]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_lookup_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | compareAndSet v e_loc e_cmp e_val =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      have h_value := undef_iff_exists_val.mp h_alloc
      obtain ⟨q, h_value⟩ := h_value
      by_cases h_q : q = (e_cmp s.stack)
      case pos =>
        rw [h_q] at h_value
        rw [step_cas_of_eq ⟨s.stack, heap₁⟩ _ h_l h_value]
        have h_heap : s.heap l = (e_cmp s.stack) := by
          rw [← h_union]; exact union_val_of_val h_value
        rw [step_cas_of_eq s _ h_l h_heap]
        simp only [substituteStack, substituteHeap, ge_iff_le]
        apply le_sSup_of_le
        · use (substituteLoc heap₁ l (e_val s.stack)), heap₂
          rw [substituteLoc_disjoint h_alloc]
          use h_disjoint
          rw [← h_union]
          use substituteLoc_union
        · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
          simp only [substituteStack]
          rw [substituteVar_eq_of_not_varStateRV h 1]
      case neg =>
        have h_ne_val : heap₁ l ≠ e_cmp s.stack := by
          intro h; simp only [h, val.injEq] at h_value; exact h_q h_value.symm
        rw [step_cas_of_neq ⟨s.stack, heap₁⟩ _ h_l h_alloc h_ne_val]
        have h_alloc' : s.heap l ≠ undef := by
          rw [← h_union]; exact ne_undef_of_union_of_ne_undef h_alloc
        have h_ne_val' : s.heap l ≠ e_cmp s.stack := by
          intro h; rw [← h_union, union_val_iff_of_val h_alloc] at h; exact h_ne_val h
        rw [step_cas_of_neq s _ h_l h_alloc' h_ne_val']
        simp only [substituteStack, ge_iff_le]
        apply le_sSup_of_le
        · use heap₁, heap₂, h_disjoint, h_union
        · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
          simp only [substituteStack]
          rw [substituteVar_eq_of_not_varStateRV h 0]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_cas_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | allocate v e_n =>
    by_cases h_m : ∃ m : ℕ, e_n s.stack = ↑m
    case pos =>
      obtain ⟨m, h_m⟩ := h_m
      rw [step_alloc ⟨s.stack, heap₁⟩ _ h_m]
      rw [step_alloc s _ h_m]
      apply le_sInf
      rintro _ ⟨l,h_ne_alloc, rfl⟩
      rw [← h_union, isNotAlloc_union] at h_ne_alloc
      apply le_sSup_of_le
      · use (allocateLoc heap₁ l m), heap₂
        use (disjoint_allocateLoc h_disjoint h_ne_alloc.right)
        simp only [substituteStack, allocateHeap, ← h_union]
        use allocateLoc_union
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        simp only [substituteStack]
        rw [substituteVar_eq_of_not_varStateRV h l]
        refine unit_mul_le_mul ?_ le_rfl
        apply sInf_le
        use l, h_ne_alloc.left
        simp only [allocateHeap]
    case neg =>
      simp only [not_exists] at h_m
      rw [step_alloc_of_error ⟨s.stack, heap₁⟩ _ h_m, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | free' e_loc e_n =>
    by_cases h_alloc : ∃ l : ℕ+, l = (e_loc s.stack) ∧ ∃ n : ℕ, n = (e_n s.stack) ∧ isAlloc heap₁ l n
    case pos =>
      obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h_alloc
      rw [step_free ⟨s.stack, heap₁⟩ _ h_l h_n h_alloc]
      have : isAlloc s.heap l n := by rw [← h_union]; exact isAlloc_union h_alloc
      rw [step_free _ _ h_l h_n this]
      simp only [freeHeap, ge_iff_le]
      apply le_sSup
      use (freeLoc heap₁ l n), heap₂, (disjoint_freeLoc h_disjoint)
      simp only [← h_union]
      use union_freeLoc h_alloc h_disjoint
    case neg =>
      simp only [not_exists, not_and] at h_alloc
      rw [step_free_of_error ⟨s.stack, heap₁⟩ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | probabilisticChoice e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    rw [step_probChoice, step_probChoice]
    rw [right_distrib_of_unit]
    pick_goal 2
    · simp only [Set.Icc.coe_mul, coe_symm_eq]
      exact (add_symm_mem_unitInterval _ _ _).right
    · apply add_le_add
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂
  | conditionalChoice e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    cases Bool.eq_false_or_eq_true (e s.stack) with
    | inl h_true =>
      rw [step_condChoice_left _ _ h_true]
      rw [step_condChoice_left ⟨s.stack, heap₁⟩ _ h_true]
      apply le_sSup
      use heap₁, heap₂
    | inr h_false =>
      rw [step_condChoice_right _ _ h_false]
      rw [step_condChoice_right ⟨s.stack, heap₁⟩ _ h_false]
      apply le_sSup
      use heap₁, heap₂
  | loop e c ih =>
    clear ih
    cases Bool.eq_false_or_eq_true (e s.stack) with
    | inl h_true =>
      rw [step_loop_cont _ _ h_true]
      rw [step_loop_cont ⟨s.stack, heap₁⟩ _ h_true]
      apply le_sSup
      use heap₁, heap₂
    | inr h_false =>
      rw [step_loop_term _ _ h_false]
      rw [step_loop_term ⟨s.stack, heap₁⟩ _ h_false]
      apply le_sSup
      use heap₁, heap₂
  | sequential c₁ c₂ ih₁ ih₂ =>
    clear ih₂
    cases eq_or_ne c₁ [Prog| ↓] with
    | inl h_term =>
      rw [h_term, step_sequential_term, step_sequential_term]
      apply le_sSup
      use heap₁, heap₂
    | inr h_ne_term =>
      rw [step_sequential_cont _ _ h_ne_term h_abort]
      have : `[qsl| [[inner [Prog| ↯] ]] ⋆ [[P]]] = `[qsl| qFalse] := by {
        apply funext
        intro s'
        apply le_antisymm
        · apply sSup_le
          rintro _ ⟨_, _, _, _, rfl⟩
          rw [h_abort]
          simp only [qslFalse, zero_mul, le_refl]
        · simp only [qslFalse, zero_le]
      }
      rw [step_sequential_cont _ _ h_ne_term this]
      simp only [writtenVarProgram, Set.union_inter_distrib_right, Set.union_empty_iff] at h
      specialize @ih₁ (fun c' => if c' = [Prog| ↯] then inner [Prog| ↯] else inner [Prog| [[c']] ; [[c₂]]]) h.left
      apply le_trans (ih₁ (by rw [if_pos rfl, h_abort]))
      apply monotone_step
      rw [Pi.le_def]
      intro c
      split
      · exact le_rfl
      · exact le_rfl


  | concurrent c₁ c₂ ih₁ ih₂ => sorry

end CQSL
