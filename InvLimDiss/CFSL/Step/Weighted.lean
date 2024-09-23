import InvLimDiss.CFSL.Step.Basic
import InvLimDiss.CFSL.Step.Atomic
import InvLimDiss.CFSL.Step.Concurrent
import InvLimDiss.CFSL.Step.Flow
import InvLimDiss.CFSL.Step.Sequential
import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.SL.Framing.Basic


namespace CFSL

open Syntax Semantics FSL unitInterval HeapValue State

private lemma weighted_step_fslAdd_superdistr_terminated
    (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| ↓] (fun c' => P c')]] + ~<e> ⬝ [[step [Prog| ↓] (fun c' => Q c')]]]
    ⊢ step [Prog| ↓] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  simp only [fslAdd, fslMul, fslReal, step_terminated', mul_one, fslNot]
  rw [truncatedAdd_sym_eq]

private lemma weighted_step_fslAdd_superdistr_abort
    (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| ↯] (fun c' => P c')]] + ~<e> ⬝ [[step [Prog| ↯] (fun c' => Q c')]]]
    ⊢ step [Prog| ↯] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  simp only [fslAdd, fslMul, fslReal, step_error', mul_one, fslNot]
  rw [truncatedAdd_sym_eq]

private lemma weighted_step_fslAdd_superdistr_assign (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : v ∉ (varRV (fslReal e))) :
    `[fsl| <e> ⬝ [[step [Prog| v ≔ e'] (fun c' => P c')]] + ~<e> ⬝ [[step [Prog| v ≔ e'] (fun c' => Q c')]]]
    ⊢ step [Prog| v ≔ e'] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  simp only [fslAdd, fslMul, step_assign, State.substituteStack, fslNot]
  rw [substituteVar_eq_of_not_varRV h (e' s.stack) s.stack]

private lemma weighted_step_fslAdd_superdistr_mutate (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| e_l *≔ e_v] (fun c' => P c')]] + ~<e> ⬝ [[step [Prog| e_l *≔ e_v] (fun c' => Q c')]]]
    ⊢ step [Prog| e_l *≔ e_v] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_alloc : ∃ l : ℕ+, e_l s.stack = ↑ l ∧ s.heap l ≠ undef
  case pos =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    simp only [fslAdd, fslMul, fslReal, step_mutate _ _ h_l h_alloc, State.substituteHeap, fslNot,
      le_refl]
  case neg =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
    simp only [fslAdd, fslMul, step_mutate_of_abort _ _ h_alloc, mul_zero, add_zero, le_refl]

private lemma weighted_step_fslAdd_superdistr_lookup (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : v ∉ (varRV (fslReal e))) :
    `[fsl| <e> ⬝ [[step [Prog| v ≔* e_l] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| v ≔* e_l] (fun c' => Q c')]]]
    ⊢ step [Prog| v ≔* e_l] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_alloc : ∃ l : ℕ+, e_l s.stack = ↑ l ∧ s.heap l ≠ undef
  case pos =>
    conv at h_alloc => right; intro l; rw [neq_undef_iff_exists_val]
    obtain ⟨l, h_l, q, h_alloc⟩ := h_alloc
    simp only [fslAdd, fslMul, step_lookup _ _ h_l h_alloc, State.substituteStack, fslNot]
    rw [substituteVar_eq_of_not_varRV h q s.stack]
  case neg =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
    simp only [fslAdd, fslMul, step_lookup_of_abort _ _ h_alloc, mul_zero, add_zero, le_refl]

private lemma weighted_step_fslAdd_superdistr_cas (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : v ∉ (varRV (fslReal e))) :
    `[fsl| <e> ⬝ [[step [Prog| v ≔ cas(e_l, e_c, e_s)] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| v ≔ cas(e_l, e_c, e_s)] (fun c' => Q c')]]]
    ⊢ step [Prog| v ≔ cas(e_l, e_c, e_s)] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_alloc : ∃ l : ℕ+, e_l s.stack = ↑ l ∧ s.heap l ≠ undef
  case pos =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    obtain ⟨q, h_q⟩ := neq_undef_iff_exists_val.mp h_alloc
    by_cases h_cmp : e_c s.stack = q
    case pos =>
      rw [← h_cmp] at h_q
      simp only [fslAdd, fslMul, step_cas_of_eq _ _ h_l h_q, State.substituteStack,
        State.substituteHeap, fslNot]
      rw [substituteVar_eq_of_not_varRV h 1 s.stack]
      simp only [fslReal, le_refl]
    case neg =>
      have h_ne_val : s.heap l ≠ e_c s.stack := by
        intro h; rw [h, val.injEq] at h_q; exact h_cmp h_q
      simp only [fslAdd, fslMul, step_cas_of_neq _ _ h_l h_alloc h_ne_val, State.substituteStack,
        fslNot, ge_iff_le]
      rw [substituteVar_eq_of_not_varRV h 0 s.stack]
  case neg =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
    simp only [fslAdd, fslMul, step_cas_of_abort _ _ h_alloc, mul_zero, add_zero, le_refl]

private lemma weighted_step_fslAdd_superdistr_allocate (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : v ∉ (varRV (fslReal e))) :
    `[fsl| <e> ⬝ [[step [Prog| v ≔ alloc(e_n)] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| v ≔ alloc(e_n)] (fun c' => Q c')]]]
    ⊢ step [Prog| v ≔ alloc(e_n)] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_n : ∃ n : ℕ, e_n s.stack = n
  case pos =>
    obtain ⟨n, h_n⟩ := h_n
    simp only [fslAdd, fslMul, step_alloc _ _ h_n, State.substituteStack, State.allocateHeap, fslNot]
    apply le_sInf
    rintro _ ⟨l, h_l, rfl⟩
    apply truncatedAdd_le_truncatedAdd
    · rw [substituteVar_eq_of_not_varRV h l s.stack]
      simp only [fslReal]
      apply unit_mul_le_mul le_rfl
      apply sInf_le
      use l, h_l
    · rw [substituteVar_eq_of_not_varRV h l s.stack]
      simp only [fslReal]
      apply unit_mul_le_mul le_rfl
      apply sInf_le
      use l, h_l
  case neg =>
    simp only [not_exists] at h_n
    simp only [fslAdd, fslMul, step_alloc_of_abort _ _ h_n, mul_zero, add_zero, le_refl]

private lemma weighted_step_fslAdd_superdistr_free (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| free(e_l, e_n)] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| free(e_l, e_n)] (fun c' => Q c')]]]
    ⊢ step [Prog| free(e_l, e_n)] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_alloc : ∃ l : ℕ+, l = e_l s.stack ∧ ∃ n : ℕ, n = e_n s.stack ∧ isAlloc s.heap l n
  case pos =>
    obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h_alloc
    simp only [fslAdd, fslMul, fslReal, step_free _ _ h_l h_n h_alloc, freeHeap, fslNot,
      le_refl]
  case neg =>
    simp only [not_exists, not_and] at h_alloc
    simp only [fslAdd, fslMul, step_free_of_abort _ _ h_alloc, mul_zero, add_zero, le_refl]

private lemma weighted_step_fslAdd_superdistr_pchoice (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| pif e_p then [[c₁]] else [[c₂]] fi] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| pif e_p then [[c₁]] else [[c₂]] fi] (fun c' => Q c')]]]
    ⊢ step [Prog| pif e_p then [[c₁]] else [[c₂]] fi] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  simp only [fslAdd, fslMul, step_probChoice]
  split_ifs
  case pos => simp only [add_zero, mul_zero, le_refl]
  case neg =>
    simp only [fslReal, zero_add, fslNot]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    apply truncatedAdd_le_truncatedAdd
    · rw [← mul_assoc, mul_comm (e s.stack), mul_assoc]
    · rw [← mul_assoc, mul_comm (σ <| e s.stack), mul_assoc]
  case pos =>
    simp only [add_zero, fslNot, fslReal]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    apply truncatedAdd_le_truncatedAdd
    · rw [← mul_assoc, mul_comm (e s.stack), mul_assoc]
    · rw [← mul_assoc, mul_comm (σ <| e s.stack), mul_assoc]
  case neg =>
    simp only [fslReal, fslNot]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    rw [left_distrib_of_unit _ _ _ (weighted_is_unit _ _ _)]
    conv => right; rw [truncatedAdd_assoc]; right; rw [← truncatedAdd_assoc]; left; rw [truncatedAdd_comm]
    conv => left; rw [truncatedAdd_assoc]
    apply truncatedAdd_le_truncatedAdd
    · rw [← mul_assoc, mul_comm (e s.stack), mul_assoc]
    · rw [truncatedAdd_assoc]
      apply truncatedAdd_le_truncatedAdd
      · rw [← mul_assoc, mul_comm (e s.stack), mul_assoc]
      · apply truncatedAdd_le_truncatedAdd
        · rw [← mul_assoc, mul_comm (σ <| e s.stack), mul_assoc]
        · rw [← mul_assoc, mul_comm (σ <| e s.stack), mul_assoc]



private lemma weighted_step_fslAdd_superdistr_condchoice (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| if e_c then [[c₁]] else [[c₂]] fi] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| if e_c then [[c₁]] else [[c₂]] fi] (fun c' => Q c')]]]
    ⊢ step [Prog| if e_c then [[c₁]] else [[c₂]] fi] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_c : e_c s.stack
  case pos =>
    simp only [fslAdd, fslMul, step_condChoice_left _ _ h_c, mul_ite, mul_zero]
    split_ifs
    case pos => simp only [add_zero, le_refl]
    case neg => rfl
  case neg =>
    simp only [Bool.not_eq_true] at h_c
    simp only [fslAdd, fslMul, step_condChoice_right _ _ h_c, mul_ite, mul_zero]
    split_ifs
    case pos => simp only [add_zero, le_refl]
    case neg => rfl

private lemma weighted_step_fslAdd_superdistr_loop (e : ProbExp Var) (P Q : Program Var → StateRV Var) :
    `[fsl| <e> ⬝ [[step [Prog| while e_c begin [[c₁]] fi] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| while e_c begin [[c₁]] fi] (fun c' => Q c')]]]
    ⊢ step [Prog| while e_c begin [[c₁]] fi] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  by_cases h_c : e_c s.stack
  case pos =>
    simp only [fslAdd, fslMul, step_loop_cont _ _ h_c, le_refl]
  case neg =>
    simp only [Bool.not_eq_true] at h_c
    simp only [fslAdd, fslMul, step_loop_term _ _ h_c, le_refl]

private lemma weighted_step_fslAdd_superdistr_sequential (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : wrtStmt c₁ ∩ varRV `[fsl| <e> ] = ∅)
    (ih : ∀ (P Q : Program Var → StateRV Var), wrtStmt c₁ ∩ varRV `[fsl| <e> ] = ∅ →
      (`[fsl| (<e> ⬝ [[step c₁ fun c' ↦ P c']]) + (~<e> ⬝ [[step c₁ fun c' ↦ Q c']]) ]) ⊢
      step c₁ fun c' ↦ `[fsl| (<e> ⬝ [[P c']]) + (~<e> ⬝ [[Q c']]) ]) :
    `[fsl| <e> ⬝ [[step [Prog| [[c₁]] ; [[c₂]]] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| [[c₁]] ; [[c₂]]] (fun c' => Q c')]]]
    ⊢ step [Prog| [[c₁]] ; [[c₂]]] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  cases eq_or_ne c₁ [Prog| ↓]
  case inl h_term =>
    simp only [fslAdd, fslMul, h_term, step_sequential_term _ _, mul_ite, mul_zero]
    split_ifs
    case pos => simp only [add_zero, le_refl]
    case neg => rfl
  case inr h_ne_term =>
    cases eq_or_ne c₁ [Prog| ↯]
    case inl h_abort =>
      simp only [fslAdd, fslMul, h_abort, step_sequential_abort _ _, mul_zero, add_zero, le_refl]
    case inr h_ne_abort =>
      simp only [fslAdd, fslMul, step_sequential_cont _ _ h_ne_term h_ne_abort]
      exact (ih _ _ h s)

private lemma weighted_step_fslAdd_superdistr_concurrent (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h₁ : wrtStmt c₁ ∩ varRV `[fsl| <e> ] = ∅) (h₂ : wrtStmt c₂ ∩ varRV `[fsl| <e> ] = ∅)
    (ih₁ : ∀ (P Q : Program Var → StateRV Var), wrtStmt c₁ ∩ varRV `[fsl| <e> ] = ∅ →
    (`[fsl| (<e> ⬝ [[step c₁ fun c' ↦ P c']]) + (~<e> ⬝ [[step c₁ fun c' ↦ Q c']]) ]) ⊢
      step c₁ fun c' ↦ `[fsl| (<e> ⬝ [[P c']]) + (~<e> ⬝ [[Q c']]) ])
    (ih₂ : ∀ (P Q : Program Var → StateRV Var), wrtStmt c₂ ∩ varRV `[fsl| <e> ] = ∅ →
    (`[fsl| (<e> ⬝ [[step c₂ fun c' ↦ P c']]) + (~<e> ⬝ [[step c₂ fun c' ↦ Q c']]) ]) ⊢
      step c₂ fun c' ↦ `[fsl| (<e> ⬝ [[P c']]) + (~<e> ⬝ [[Q c']]) ]):
    `[fsl| <e> ⬝ [[step [Prog| [[c₁]] || [[c₂]]] (fun c' => P c')]]
      + ~<e> ⬝ [[step [Prog| [[c₁]] || [[c₂]]] (fun c' => Q c')]]]
    ⊢ step [Prog| [[c₁]] || [[c₂]]] (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  intro s
  cases eq_or_ne c₁ [Prog| ↯]
  case inl h_abort₁ =>
    simp only [fslAdd, fslMul, h_abort₁, step_concurrent_abort_left, mul_zero, add_zero, le_refl]
  case inr h_ne_abort₁ =>
    cases eq_or_ne c₂ [Prog| ↯]
    case inl h_abort₂ =>
      simp only [fslAdd, fslMul, h_abort₂, step_concurrent_abort_right, mul_zero, add_zero, le_refl]
    case inr h_ne_abort₂ =>
      cases eq_or_ne c₁ [Prog| ↓]
      case inl h_term₁ =>
        cases eq_or_ne c₂ [Prog| ↓]
        case inl h_term₂ =>
          simp only [fslAdd, fslMul, h_term₁, h_term₂, step_concurrent_term, le_refl]
        case inr h_ne_term₂ =>
          simp only [fslAdd, fslMul, h_term₁,
            step_concurrent_cont_only_right _ _ h_ne_term₂ h_ne_abort₂]
          exact ih₂ _ _ h₂ s
      case inr h_ne_term₁ =>
        cases eq_or_ne c₂ [Prog| ↓]
        case inl h_term₂ =>
          simp only [fslAdd, fslMul, h_term₂,
            step_concurrent_cont_only_left _ _ h_ne_term₁ h_ne_abort₁]
          exact ih₁ _ _ h₁ s
        case inr h_ne_term₂ =>
          simp only [fslAdd, fslMul,
            step_concurrent_cont _ _ h_ne_term₁ h_ne_term₂ h_ne_abort₁ h_ne_abort₂, le_min_iff]
          constructor
          · apply le_trans ?_ (ih₁ _ _ h₁ s)
            apply truncatedAdd_le_truncatedAdd
            · simp only [fslMul]
              apply unit_mul_le_mul le_rfl
              apply min_le_left
            · simp only [fslMul]
              apply unit_mul_le_mul le_rfl
              apply min_le_left
          · apply le_trans ?_ (ih₂ _ _ h₂ s)
            apply truncatedAdd_le_truncatedAdd
            · simp only [fslMul]
              apply unit_mul_le_mul le_rfl
              apply min_le_right
            · simp only [fslMul]
              apply unit_mul_le_mul le_rfl
              apply min_le_right

theorem weighted_step_fslAdd_superdistr (e : ProbExp Var) (P Q : Program Var → StateRV Var)
    (h : (wrtStmt c) ∩ (varRV (fslReal e)) = ∅) :
    `[fsl| <e> ⬝ [[step c (fun c' => P c')]] + ~<e> ⬝ [[step c (fun c' => Q c')]]]
    ⊢ step c (fun c' => `[fsl| <e> ⬝ [[P c']] + ~<e> ⬝ [[Q c']]]) := by
  induction c generalizing P Q with
  | terminated => exact weighted_step_fslAdd_superdistr_terminated _ _ _
  | abort => exact weighted_step_fslAdd_superdistr_abort _ _ _
  | skip' => simp only [step_skip']; exact le_rfl
  | assign v e' =>
    simp only [wrtStmt, Set.singleton_inter_eq_empty] at h
    exact weighted_step_fslAdd_superdistr_assign _ _ _ h
  | mutate e_l e_v => exact weighted_step_fslAdd_superdistr_mutate _ _ _
  | lookup v e_l =>
    simp only [wrtStmt, Set.singleton_inter_eq_empty] at h
    exact weighted_step_fslAdd_superdistr_lookup _ _ _ h
  | compareAndSet v e_loc e_cmp e_set =>
    simp only [wrtStmt, Set.singleton_inter_eq_empty] at h
    exact weighted_step_fslAdd_superdistr_cas _ _ _ h
  | allocate v e_n =>
    simp only [wrtStmt, Set.singleton_inter_eq_empty] at h
    exact weighted_step_fslAdd_superdistr_allocate _ _ _ h
  | free' e_l e_n =>
    exact weighted_step_fslAdd_superdistr_free _ _ _
  | probabilisticBranching e_p c₁ c₂ =>
    exact weighted_step_fslAdd_superdistr_pchoice _ _ _
  | conditionalBranching e_c c₁ c₂ =>
    exact weighted_step_fslAdd_superdistr_condchoice _ _ _
  | loop e_c c =>
    exact weighted_step_fslAdd_superdistr_loop _ _ _
  | sequential c₁ c₂ ih₁ =>
    simp only [wrtStmt] at h
    exact weighted_step_fslAdd_superdistr_sequential _ _ _ h ih₁
  | concurrent c₁ c₂ ih₁ ih₂ =>
    simp only [wrtStmt, Set.union_inter_distrib_right, Set.union_empty_iff] at h
    exact weighted_step_fslAdd_superdistr_concurrent _ _ _ h.left h.right ih₁ ih₂

end CFSL
