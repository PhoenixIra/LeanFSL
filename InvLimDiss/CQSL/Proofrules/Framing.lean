import InvLimDiss.CQSL.Step.Atomic
import InvLimDiss.CQSL.Step.Flow
import InvLimDiss.CQSL.Step.Sequential
import InvLimDiss.CQSL.Step.Concurrent
import InvLimDiss.CQSL.WeakPre
import InvLimDiss.SL.Framing.Basic

namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical


-- todo: write for each program instead of one big

theorem step_framing_of_term (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| ↓]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| ↓]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
  rw [step_terminated, step_terminated]; exact le_one'

theorem step_framing_of_abort (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| ↯]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| ↯]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
  rw [step_error, step_error]; exact le_one'

theorem step_framing_of_skip (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| skip]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| skip]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
  rw [step_skip, step_skip]
  apply le_sSup
  use heap₁, heap₂

theorem step_framing_of_assign (inner : Program Var → StateRV Var)
    (h : v ∉ varStateRV P) :
    `[qsl| [[step ([Prog| v ≔ e]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| v ≔ e]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  rw [step_assign, step_assign]
  apply le_sSup_of_le
  use heap₁, heap₂, h_disjoint, h_union
  rw [Subtype.mk_le_mk]
  simp only [substituteStack, Set.Icc.coe_mul]
  rw [substituteVar_eq_of_not_varStateRV h (e s.stack)]

theorem step_framing_of_manipulate (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| e_loc *≔ e_val]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| e_loc *≔ e_val]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
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
      rw [step_manipulate_of_abort _ _ h_alloc]
      simp only [zero_mul, zero_le]

theorem step_framing_of_lookup (inner : Program Var → StateRV Var)
    (h : v ∉ varStateRV P) :
    `[qsl| [[step ([Prog| v ≔* e_loc]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| v ≔* e_loc]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
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
    · simp only [substituteStack]
      rw [substituteVar_eq_of_not_varStateRV h q]
  case neg =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
    rw [step_lookup_of_abort _ _ h_alloc]
    simp only [zero_mul, zero_le]

theorem step_framing_of_cas (inner : Program Var → StateRV Var)
    (h : v ∉ varStateRV P) :
    `[qsl| [[step ([Prog| v ≔ cas(e_loc, e_cmp, e_val)]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| v ≔ cas(e_loc, e_cmp, e_val)]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
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
      · simp only [substituteStack]
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
      · simp only [substituteStack]
        rw [substituteVar_eq_of_not_varStateRV h 0]
  case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_cas_of_abort _ _ h_alloc]
      simp only [zero_mul, zero_le]

theorem step_framing_of_allocate (inner : Program Var → StateRV Var)
    (h : v ∉ varStateRV P) :
    `[qsl| [[step ([Prog| v ≔ alloc(e)]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| v ≔ alloc(e)]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  by_cases h_m : ∃ m : ℕ, e s.stack = ↑m
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
    · simp only [substituteStack]
      rw [substituteVar_eq_of_not_varStateRV h l]
      refine unit_mul_le_mul ?_ le_rfl
      apply sInf_le
      use l, h_ne_alloc.left
      simp only [allocateHeap]
  case neg =>
    simp only [not_exists] at h_m
    rw [step_alloc_of_abort ⟨s.stack, heap₁⟩ _ h_m]
    simp only [zero_mul, zero_le]

theorem step_framing_of_free (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| free(e_loc, e_n)]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| free(e_loc, e_n)]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
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
    rw [step_free_of_error ⟨s.stack, heap₁⟩ _ h_alloc]
    simp only [zero_mul, zero_le]

theorem step_framing_of_probBranching (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| pif e then [[c₁]] else [[c₂]] fi]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| pif e then [[c₁]] else [[c₂]] fi]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  rw [step_probChoice, step_probChoice]
  rw [right_distrib_of_unit]
  pick_goal 2
  · simp only [Set.Icc.coe_mul, coe_symm_eq]
    split_ifs
    · simp only [Set.Icc.coe_zero, add_zero, zero_le_one]
    · simp only [Set.Icc.coe_zero, zero_add]
      exact le_one'
    · simp only [Set.Icc.coe_zero, add_zero]
      exact le_one'
    · exact (add_symm_mem_unitInterval _ _ _).right
  · split_ifs
    · simp only [zero_mul, add_zero, le_refl]
    · simp only [zero_mul, zero_add]
      rw [mul_assoc]
      refine mul_le_mul le_rfl ?_ nonneg' nonneg'
      apply le_sSup
      use heap₁, heap₂
    · simp only [zero_mul, add_zero]
      rw [mul_assoc]
      refine mul_le_mul le_rfl ?_ nonneg' nonneg'
      apply le_sSup
      use heap₁, heap₂
    · apply add_le_add
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂

theorem step_framing_of_condBranching (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| if e then [[c₁]] else [[c₂]] fi]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| if e then [[c₁]] else [[c₂]] fi]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  cases Bool.eq_false_or_eq_true (e s.stack) with
    | inl h_true =>
      rw [step_condChoice_left _ _ h_true]
      rw [step_condChoice_left ⟨s.stack, heap₁⟩ _ h_true]
      split_ifs
      · simp only [zero_mul, le_refl]
      · apply le_sSup
        use heap₁, heap₂
    | inr h_false =>
      rw [step_condChoice_right _ _ h_false]
      rw [step_condChoice_right ⟨s.stack, heap₁⟩ _ h_false]
      split_ifs
      · simp only [zero_mul, le_refl]
      · apply le_sSup
        use heap₁, heap₂

theorem step_framing_of_loop (inner : Program Var → StateRV Var) :
    `[qsl| [[step ([Prog| while e begin [[c]] fi]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| while e begin [[c]] fi]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
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

theorem step_framing_of_sequential (inner : Program Var → StateRV Var)
    (ih : `[qsl| [[step c₁ fun c' ↦ inner [Prog| [[c']] ; [[c₂]]] ]] ⋆ [[P]] ]
          ⊢ step c₁ fun c' ↦ `[qsl| [[inner [Prog| [[c']] ; [[c₂]]] ]] ⋆ [[P]] ]) :
    `[qsl| [[step ([Prog| [[c₁]] ; [[c₂]]]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| [[c₁]] ; [[c₂]]]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  cases eq_or_ne c₁ [Prog| ↓] with
  | inl h_term =>
    rw [h_term, step_sequential_term, step_sequential_term]
    split_ifs
    · simp only [zero_mul, le_refl]
    · apply le_sSup
      use heap₁, heap₂
  | inr h_term =>
    cases eq_or_ne c₁ [Prog| ↯] with
    | inl h_abort =>
      rw [h_abort, step_sequential_abort]
      simp only [zero_mul, zero_le]
    | inr h_abort =>
      rw [step_sequential_cont _ _ h_term h_abort]
      rw [step_sequential_cont _ _ h_term h_abort]
      refine le_trans ?_ (ih s)
      apply le_sSup
      use heap₁, heap₂

theorem step_framing_of_concurrent (inner : Program Var → StateRV Var)
    (ih₁ : `[qsl| [[step c₁ fun c' ↦ inner [Prog| [[c']] || [[c₂]]] ]] ⋆ [[P]] ]
          ⊢ step c₁ fun c' ↦ `[qsl| [[inner [Prog| [[c']] || [[c₂]]] ]] ⋆ [[P]] ])
    (ih₂ : `[qsl| [[step c₂ fun c' ↦ inner [Prog| [[c₁]] || [[c']]] ]] ⋆ [[P]] ]
          ⊢ step c₂ fun c' ↦ `[qsl| [[inner [Prog| [[c₁]] || [[c']]] ]] ⋆ [[P]] ]) :
    `[qsl| [[step ([Prog| [[c₁]] || [[c₂]]]) (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step ([Prog| [[c₁]] || [[c₂]]]) (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  cases eq_or_ne c₁ [Prog| ↯] with
  | inl h_c₁ =>
    rw [h_c₁, step_concurrent_abort_left]
    simp only [zero_mul, zero_le]
  | inr h_c₁_ne_abort =>
    cases eq_or_ne c₂ [Prog| ↯] with
    | inl h_c₂ =>
      rw [h_c₂, step_concurrent_abort_right]
      simp only [zero_mul, zero_le]
    | inr h_c₂_ne_abort =>
      cases eq_or_ne c₁ [Prog| ↓] with
      | inl h_c₁ =>
        rw [h_c₁]
        cases eq_or_ne c₂ [Prog| ↓] with
        | inl h_c₂ =>
          rw [h_c₂, step_concurrent_term, step_concurrent_term]
          apply le_sSup
          use heap₁, heap₂
        | inr h_c₂_ne_term =>
          rw [step_concurrent_cont_only_right ⟨s.stack, heap₁⟩ _ h_c₂_ne_term h_c₂_ne_abort]
          rw [step_concurrent_cont_only_right s _ h_c₂_ne_term h_c₂_ne_abort]
          rw [← h_c₁]
          refine le_trans ?_ (ih₂ s)
          apply le_sSup
          use heap₁, heap₂
      | inr h_c₁_ne_term =>
        cases eq_or_ne c₂ [Prog| ↓] with
        | inl h_c₂ =>
          rw [h_c₂]
          rw [step_concurrent_cont_only_left ⟨s.stack, heap₁⟩ _ h_c₁_ne_term h_c₁_ne_abort]
          rw [step_concurrent_cont_only_left s _ h_c₁_ne_term h_c₁_ne_abort]
          rw [← h_c₂]
          refine le_trans ?_ (ih₁ s)
          apply le_sSup
          use heap₁, heap₂
        | inr h_c₂_ne_term =>
          rw [step_concurrent_cont ⟨s.stack, heap₁⟩ _
            h_c₁_ne_term h_c₂_ne_term h_c₁_ne_abort h_c₂_ne_abort]
          rw [step_concurrent_cont s _
            h_c₁_ne_term h_c₂_ne_term h_c₁_ne_abort h_c₂_ne_abort]
          apply le_min
          · refine le_trans ?_ (ih₁ s)
            apply le_sSup_of_le
            use heap₁, heap₂, h_disjoint, h_union
            refine unit_mul_le_mul ?_ le_rfl
            exact le_trans (min_le_left _ _) le_rfl
          · refine le_trans ?_ (ih₂ s)
            apply le_sSup_of_le
            use heap₁, heap₂, h_disjoint, h_union
            refine unit_mul_le_mul ?_ le_rfl
            exact le_trans (min_le_right _ _) le_rfl

theorem step_framing (inner : Program Var → StateRV Var)
    (h : (writtenVarProgram c) ∩ (varStateRV P) = ∅) :
    `[qsl| [[step c (fun c' => inner c')]] ⋆ [[P]]]
      ⊢ step c (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  induction c generalizing inner with
  | terminated => exact step_framing_of_term inner
  | abort => exact step_framing_of_abort inner
  | skip' => exact step_framing_of_skip inner
  | assign v e =>
    simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
    exact step_framing_of_assign inner h
  | manipulate e_loc e_val => exact step_framing_of_manipulate inner
  | lookup v e_loc =>
    simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
    exact step_framing_of_lookup inner h
  | compareAndSet v e_loc e_cmp e_val =>
    simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
    exact step_framing_of_cas inner h
  | allocate v e_n =>
    simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
    exact step_framing_of_allocate inner h
  | free' e_loc e_n => exact step_framing_of_free inner
  | probabilisticBranching e c₁ c₂ => exact step_framing_of_probBranching inner
  | conditionalBranching e c₁ c₂ => exact step_framing_of_condBranching inner
  | loop e c => exact step_framing_of_loop inner
  | sequential c₁ c₂ ih₁ ih₂ =>
    clear ih₂
    simp only [writtenVarProgram, Set.union_inter_distrib_right, Set.union_empty_iff] at h
    exact step_framing_of_sequential inner (ih₁ _ h.left)
  | concurrent c₁ c₂ ih₁ ih₂ =>
    simp only [writtenVarProgram, Set.union_inter_distrib_right, Set.union_empty_iff] at h
    apply step_framing_of_concurrent
    · exact ih₁ _ h.left
    · exact ih₂ _ h.right

open OrderHom

theorem wrlp_frame
    (h : (writtenVarProgram c) ∩ (varStateRV P) = ∅) :
    `[qsl| wrlp [c] ([[P]] | [[RI]]) ⋆ [[F]] ⊢ wrlp [c] ([[P]] ⋆ [[F]] | [[RI]])] := by
  sorry



end CQSL
