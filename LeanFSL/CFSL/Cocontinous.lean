import LeanFSL.CFSL.WeakExpectation
import LeanFSL.Mathlib.FixedPoints
import LeanFSL.CFSL.Bellman
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder

namespace CFSL

open OmegaCompletePartialOrder FSL Syntax Semantics Bellman State

theorem wrleFinite₂ (c : Program Var) (s : State Var) (a : Action) (h_a : a ∈ enabledAction c s) :
    ∃ i j : unitInterval, ∃ c₁ c₂ : Program Var, ∃ σ₁ σ₂ : State Var, ∀ post : Program Var → StateRV Var,
    ∑' (cs : reachState Var), semantics c s a cs.prog cs.state * post cs.prog cs.state
    = i * post c₁ σ₁ + j * post c₂ σ₂ := by
  induction c generalizing a with
  | terminated => simp only [enabledAction, Set.mem_empty_iff_false] at h_a
  | abort => simp only [enabledAction, Set.mem_empty_iff_false] at h_a
  | skip' =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    use 1, 0, [Prog| ↓], [Prog| skip], s, s
    intro post
    rw [tsum_skip_of_deterministic]
    simp only [one_mul, zero_mul, add_zero]
  | assign v e =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    use 1, 0, [Prog| ↓], [Prog| skip], (s.substituteStack v (e s.stack)), s
    intro post
    rw [tsum_assign_of_deterministic]
    simp only [State.substituteStack, one_mul, zero_mul, add_zero]
  | mutate e_loc e_val =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : ∃ l : ℕ+, e_loc s.stack = ↑l ∧ s.heap l ≠ HeapValue.undef
    case pos =>
      obtain ⟨l, h_l, h_def⟩ := h
      use 1, 0, [Prog| ↓], [Prog| skip], (s.substituteHeap l (e_val s.stack)), s
      intro post
      rw [tsum_mutate_of_deterministic s post h_l h_def]
      simp only [State.substituteHeap, one_mul, zero_mul, add_zero]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h
      use 0, 0, [Prog| skip], [Prog| skip], s, s
      intro post
      rw [tsum_mutate_of_deterministic_of_abort s post h]
      simp only [zero_mul, add_zero]
  | lookup v e_loc =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : ∃ l : ℕ+, e_loc s.stack = ↑l ∧ s.heap l ≠ HeapValue.undef
    case pos =>
      obtain ⟨l, h_l, h_def⟩ := h
      rw [neq_undef_iff_exists_val] at h_def
      obtain ⟨q, h_def⟩ := h_def
      use 1, 0, [Prog| ↓], [Prog| skip], (s.substituteStack v q), s
      intro post
      rw [tsum_lookup_of_deterministic s post h_l h_def]
      simp only [State.substituteStack, one_mul, zero_mul, add_zero]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h
      use 0, 0, [Prog| skip], [Prog| skip], s, s
      intro post
      rw [tsum_lookup_of_deterministic_of_abort s post h]
      simp only [zero_mul, add_zero]
  | compareAndSet v e_loc e_cmp e_val =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : ∃ l : ℕ+, e_loc s.stack = ↑l ∧ s.heap l ≠ HeapValue.undef
    case pos =>
      obtain ⟨l, h_l, h_def⟩ := h
      by_cases h : s.heap l = e_cmp s.stack
      case pos =>
        use 1, 0, [Prog| ↓], [Prog| skip],
          ((s.substituteHeap l (e_val s.stack)).substituteStack v 1), s
        intro post
        rw [tsum_cas_of_eq_of_deterministic s post h_l h]
        simp only [State.substituteStack, State.substituteHeap, one_mul, zero_mul, add_zero]
      case neg =>
        use 1, 0, [Prog| ↓], [Prog| skip],
          (s.substituteStack v 0), s
        intro post
        rw [tsum_cas_of_neq_of_deterministic s post h_l h_def h]
        simp only [State.substituteStack, one_mul, zero_mul, add_zero]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h
      use 0, 0, [Prog| skip], [Prog| skip], s, s
      intro post
      rw [tsum_cas_of_deterministic_of_abort s post h]
      simp only [zero_mul, add_zero]
  | allocate v e =>
    simp only [enabledAction] at h_a
    by_cases h : ∃ n : ℕ, n = e s.stack
    case pos =>
      simp only [if_pos h, Set.mem_setOf_eq] at h_a
      obtain ⟨l, h_a, n, h_n, h_alloc⟩ := h_a
      rw [h_a]
      use 1, 0, [Prog| ↓], [Prog| skip], ((s.allocateHeap l n).substituteStack v ↑↑l), s
      intro post
      rw [tsum_alloc_of_allocation s post h_n.symm h_alloc]
      simp only [State.substituteStack, State.allocateHeap, one_mul, zero_mul, add_zero]
    case neg =>
      simp only [if_neg h, Set.mem_singleton_iff] at h_a
      rw [h_a]
      use 0, 0, [Prog| skip], [Prog| skip], s, s
      intro post
      rw [tsum_alloc_of_deterministic_of_abort]
      simp only [zero_mul, add_zero]
  | free' e_loc e_n =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : ∃ l : ℕ+, l = e_loc s.stack ∧ ∃ n : ℕ, n = e_n s.stack ∧ isAlloc s.heap l n
    case pos =>
      obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h
      use 1, 0, [Prog| ↓], [Prog| skip], s.freeHeap l n, s
      intro post
      rw [tsum_free_of_deterministic _ _ h_l h_n h_alloc]
      simp only [freeHeap, one_mul, zero_mul, add_zero]
    case neg =>
      simp only [not_exists, not_and] at h
      use 0, 0, [Prog| skip], [Prog| skip], s, s
      intro post
      rw [tsum_free_of_deterministic_of_error _ _ h]
      simp only [zero_mul, add_zero]
  | probabilisticBranching e c₁ c₂ _ _ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    classical
    use (if c₁ = [Prog| ↯] then 0 else e s.stack)
    use (if c₂ = [Prog| ↯] then 0 else unitInterval.symm (e s.stack))
    use c₁, c₂, s, s
    intro post
    rw [tsum_probChoice_of_deterministic]
    simp only [ite_mul, zero_mul]
  | conditionalBranching e c₁ c₂ _ _ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : e s.stack
    case pos =>
      classical
      use (if c₁ = [Prog| ↯] then 0 else 1), 0, c₁, [Prog| skip], s, s
      intro post
      rw [tsum_condChoice_left_of_deterministic _ _ h]
      simp only [ite_mul, zero_mul, one_mul, add_zero]
    case neg =>
      simp only [Bool.not_eq_true] at h
      classical
      use (if c₂ = [Prog| ↯] then 0 else 1), 0, c₂, [Prog| skip], s, s
      intro post
      rw [tsum_condChoice_right_of_deterministic _ _ h]
      simp only [ite_mul, zero_mul, one_mul, add_zero]
  | loop e c _ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    by_cases h : e s.stack
    case pos =>
      use 1, 0, [Prog| [[c]] ; while e begin [[c]] fi], [Prog| skip], s, s
      intro post
      rw [tsum_loop_cont_of_deterministic _ _ h]
      simp only [one_mul, zero_mul, add_zero]
    case neg =>
      simp only [Bool.not_eq_true] at h
      use 1, 0, [Prog| ↓], [Prog| skip], s, s
      intro post
      rw [tsum_loop_term_of_deterministic _ _ h]
      simp only [one_mul, zero_mul, add_zero]
  | sequential c₁ c₂ ih₁ _ =>
    simp only [enabledAction] at h_a
    by_cases h : c₁ = [Prog| ↓] ∨ c₁ = [Prog| ↯]
    case pos =>
      cases h
      case inl h =>
        simp only [h, reduceCtorEq, or_false, ↓reduceIte, Set.mem_singleton_iff] at h_a
        rw [h_a, h]
        classical
        use (if c₂ = [Prog| ↯] then 0 else 1), 0, c₂, [Prog| skip], s, s
        intro post
        rw [tsum_sequential_term_of_deterministic]
        simp only [ite_mul, zero_mul, one_mul, add_zero]
      case inr h =>
        simp only [h, reduceCtorEq, or_true, ↓reduceIte, Set.mem_singleton_iff] at h_a
        rw [h_a, h]
        use 0, 0, [Prog| skip], [Prog| skip], s, s
        intro post
        rw [tsum_sequential_abort_of_deterministic]
        simp only [zero_mul, add_zero]
    case neg =>
      simp only [h, ↓reduceIte] at h_a
      simp only [not_or] at h
      specialize ih₁ a h_a
      obtain ⟨i, j, c₁', c₁'', s₁, s₂, ih⟩ := ih₁
      use i, j, [Prog| [[c₁']] ; [[c₂]]], [Prog| [[c₁'']] ; [[c₂]]], s₁, s₂
      intro post
      rw [tsum_sequential_cont _ _ h.left h.right]
      rw [ih (fun c s => post ([Prog| [[c]] ; [[c₂]]]) s)]
  | concurrent c₁ c₂ ih₁ ih₂ =>
    simp only [enabledAction] at h_a
    by_cases h : c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] ∨ c₁ = [Prog| ↯] ∨ c₂ = [Prog| ↯]
    case pos =>
      cases h
      case inl h =>
        simp only [h, and_self, reduceCtorEq, or_self, or_false, ↓reduceIte,
          Set.mem_singleton_iff] at h_a
        rw [h.left, h.right, h_a]
        use 1, 0, [Prog| ↓], [Prog| skip], s, s
        intro post
        rw [tsum_concurrent_term_of_deterministic]
        simp only [one_mul, zero_mul, add_zero]
      case inr h =>
        cases h
        case inl h =>
          simp only [h, reduceCtorEq, false_and, true_or, or_true, ↓reduceIte,
            Set.mem_singleton_iff] at h_a
          rw [h_a, h]
          use 0, 0, [Prog| skip], [Prog| skip], s, s
          intro post
          rw [tsum_concurrent_abort_left_of_deterministic]
          simp only [zero_mul, add_zero]
        case inr h =>
          simp only [h, reduceCtorEq, and_false, or_true, ↓reduceIte, Set.mem_singleton_iff] at h_a
          rw [h_a, h]
          use 0, 0, [Prog| skip], [Prog| skip], s, s
          intro post
          rw [tsum_concurrent_abort_right_of_deterministic]
          simp only [zero_mul, add_zero]
    case neg =>
      simp only [h, ↓reduceIte, Set.mem_union, Set.mem_setOf_eq] at h_a
      obtain ⟨a', rfl, h_term, h_a'⟩ | ⟨a', rfl, h_term, h_a'⟩ := h_a
      · simp only [not_or, not_and_or] at h
        obtain ⟨_, h_c₁_abort, h_c₂_abort⟩ := h
        specialize ih₁ a' h_a'
        obtain ⟨i, j, c₁', c₁'', s₁, s₂, ih₁⟩ := ih₁
        use i, j, [Prog| [[c₁']] || [[c₂]]], [Prog| [[c₁'']] || [[c₂]]], s₁, s₂
        intro post
        rw [tsum_concurrent_cont_left _ _ h_term h_c₁_abort h_c₂_abort]
        rw [ih₁ (fun c s => post ([Prog| [[c]] || [[c₂]]]) s)]
      · simp only [not_or, not_and_or] at h
        obtain ⟨_, h_c₁_abort, h_c₂_abort⟩ := h
        specialize ih₂ a' h_a'
        obtain ⟨i, j, c₂', c₂'', s₁, s₂, ih₂⟩ := ih₂
        use i, j, [Prog| [[c₁]] || [[c₂']]], [Prog| [[c₁]] || [[c₂'']]], s₁, s₂
        intro post
        rw [tsum_concurrent_cont_right _ _ h_term h_c₁_abort h_c₂_abort]
        rw [ih₂ (fun c s => post ([Prog| [[c₁]] || [[c]]]) s)]

theorem bellmanSolution_cocontinous (post : StateRV Var) :
    ωScottContinuous (OrderHom.dual <| wrleStepHom post `[fsl| emp]) := by
  rw [dual_continuous_iff_co_continuous]
  intro chain h_chain
  apply le_antisymm
  · apply le_iInf
    intro n
    apply (wrleStepHom post `[fsl| emp]).monotone
    exact iInf_le _ _
  · intro c
    rw [iInf_apply]
    simp only [wrleStepHom, OrderHom.coe_mk, wrleStep]
    split
    case a.h_1 =>
      rw [iInf_le_iff]
      intro s h
      apply le_trans (h 0)
      rfl
    case a.h_2 =>
      rw [iInf_le_iff]
      intro s h
      apply le_trans (h 0)
      rfl
    case a.h_3 c _ _ h_c_ne_term h_c_ne_err =>
      simp only [fslSepMul_fslEmp_eq, fslEmp_fslSepDiv_eq]
      unfold step
      intro s
      simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro a h_a
      obtain ⟨i, j, c₁, c₂, σ₁, σ₂, h'⟩ := wrleFinite₂ c s a h_a
      rw [h']
      simp only [iInf_apply]
      conv => right; rw [iInf_apply, iInf_apply]
      simp only [unitInterval.mul_iInf]
      apply le_trans ?_ (unitInterval.iInf_add_le_add_iInf_of_antitone ?_ ?_)
      · rw [le_iInf_iff]
        intro n
        rw [iInf_apply]
        apply iInf_le_of_le n
        apply sInf_le
        use a, h_a
        rw [h']
      · intro n m h
        simp only
        apply unitInterval.unit_mul_le_mul le_rfl
        apply h_chain
        exact h
      · intro n m h
        simp only
        apply unitInterval.unit_mul_le_mul le_rfl
        apply h_chain
        exact h

end CFSL
