import InvLimDiss.SL.Framing.Defs


open Syntax Semantics QSL State

namespace QSL

theorem wrtStmt_subset_wrtProg :
    wrtStmt c ⊆ wrtProg c := by
  intro v h_v
  induction c with
  | sequential _ _ ih₁ _ =>
    simp only [wrtStmt] at h_v
    simp only [wrtProg, Set.mem_union]
    exact Or.inl (ih₁ h_v)
  | concurrent _ _ ih₁ ih₂ =>
    simp only [wrtStmt, Set.mem_union] at h_v
    simp only [wrtProg, Set.mem_union]
    cases h_v with
    | inl h_v => apply Or.inl (ih₁ h_v)
    | inr h_v => apply Or.inr (ih₂ h_v)
  | _ =>
    all_goals try simp only [wrtStmt, Set.mem_empty_iff_false] at h_v
    all_goals try {
      simp only [wrtProg, Set.mem_singleton_iff]
      simp only [Set.mem_singleton_iff] at h_v
      exact h_v
    }

theorem wrtStmt_inter_varRV_eq_emptyset_of_wrtProg
    (h : wrtProg c ∩ varRV F = ∅) :
    wrtStmt c ∩ varRV F = ∅ := by
  apply Set.subset_eq_empty ?_ h
  apply Set.inter_subset_inter
  . exact wrtStmt_subset_wrtProg
  · exact subset_rfl

theorem substituteStack_eq_of_not_varRV {f : StateRV Var} {v : Var} (h : v ∉ varRV f) :
    ∀ q s, f (s.substituteStack v q) = f s := by
  intro q s
  simp only [varRV, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h
  exact (h s q).symm

theorem substituteVar_eq_of_not_varRV {f : StateRV Var} {v : Var} (h : v ∉ varRV f) :
    ∀ q stack heap, f ⟨substituteVar stack v q, heap⟩ = f ⟨stack, heap⟩ := by
  intro q stack heap
  have := substituteStack_eq_of_not_varRV h q ⟨stack, heap⟩
  simp only [substituteStack] at this
  rw [this]

theorem qslSubst_eq_of_not_varRV {f : StateRV Var} {v : Var} (h : v ∉ varRV f) :
    ∀ e, `[qsl| [[f]](v ↦ e)] = f := by
  intro e
  apply funext
  intro s
  rw [qslSubst]
  exact substituteStack_eq_of_not_varRV h (e s.stack) s

theorem written_of_transition
    (h_sem : programSmallStepSemantics c s a c' s' ≠ 0) :
    wrtProg c' ⊆ wrtProg c := by
  intro v h
  induction c generalizing c' a with
  | terminated =>
    simp only [programSmallStepSemantics, Pi.zero_apply, ne_eq, not_true_eq_false] at h_sem
  | abort =>
    simp only [programSmallStepSemantics, Pi.zero_apply, ne_eq, not_true_eq_false] at h_sem
  | skip' =>
    simp only [programSmallStepSemantics, skipSmallStepSemantics, ne_eq,
      unitInterval.iteOneZero_eq_zero_def, not_and, Classical.not_imp, not_not] at h_sem
    simp only [h_sem.left, wrtProg, Set.mem_empty_iff_false] at h
  | assign v e =>
    simp only [programSmallStepSemantics, assignSmallStepSemantics, substituteStack, ne_eq] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [not_true_eq_false] at h_sem
  | mutate e e' =>
    simp only [programSmallStepSemantics, mutateSmallStepSemantics, ne_eq, substituteHeap,
      not_exists] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_3 => simp only [not_true_eq_false] at h_sem
  | lookup v e =>
    simp only [programSmallStepSemantics, lookupSmallStepSemantics, substituteStack, not_exists,
      ne_eq] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_3 => simp only [not_true_eq_false] at h_sem
  | compareAndSet v e₁ e₂ e₃ =>
    simp only [programSmallStepSemantics, compareAndSetSmallStepSemantics, substituteStack,
      substituteHeap, ne_eq, not_exists] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_3 => simp only [not_true_eq_false] at h_sem
  | allocate v e =>
    simp only [programSmallStepSemantics, allocateSmallStepSemantics, substituteStack, allocateHeap,
      not_exists, ne_eq] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_3 => simp only [not_true_eq_false] at h_sem
  | free' e e' =>
    simp only [programSmallStepSemantics, freeSmallStepSemantics, freeHeap, not_exists,
      exists_and_right, ne_eq] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_3 => simp only [not_true_eq_false] at h_sem
  | probabilisticBranching e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    simp only [wrtProg, Set.mem_union]
    simp only [programSmallStepSemantics, probabilisticBranchingSmallStepSemantics, ne_eq,
      ite_eq_right_iff, and_imp, Classical.not_imp] at h_sem
    split_ifs at h_sem
    case pos h_c' =>
      rw [h_c'.left]
      exact Or.inl h
    case pos h_c₁ =>
      rw [h_c₁]
      exact Or.inl h
    case pos h_c₂ =>
      rw [h_c₂]
      exact Or.inr h
    case neg =>
      simp only [not_true_eq_false, and_false] at h_sem
  | conditionalBranching e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    simp only [wrtProg, Set.mem_union]
    simp only [programSmallStepSemantics, conditionalBranchingSmallStepSemantics, Bool.not_eq_true,
      ne_eq, unitInterval.iteOneZero_eq_zero_def, not_not] at h_sem
    cases h_sem.right.right with
    | inl h_true =>
      rw [h_true.right]
      exact Or.inl h
    | inr h_false =>
      rw [h_false.right]
      exact Or.inr h
  | loop e c ih =>
    clear ih
    simp only [wrtProg, Set.mem_union]
    simp only [programSmallStepSemantics, loopSmallStepSemantics, Bool.not_eq_true, ne_eq] at h_sem
    split at h_sem
    case h_1 => simp only [wrtProg, Set.mem_empty_iff_false] at h
    case h_2 =>
      simp only [unitInterval.iteOneZero_eq_zero_def, not_and, Bool.not_eq_true, Classical.not_imp,
        Bool.not_eq_false] at h_sem
      rw [h_sem.right.left] at h
      simp only [wrtProg, Set.union_self] at h
      exact h
  | sequential c₁ c₂ ih₁ ih₂ =>
    clear ih₂
    simp only [wrtProg, Set.mem_union]
    rw [programSmallStepSemantics] at h_sem
    simp only at h_sem
    split_ifs at h_sem
    case pos =>
      simp only [ne_eq, unitInterval.iteOneZero_eq_zero_def, not_and, Classical.not_imp,
        not_not] at h_sem
      rw [h_sem.right.right] at h
      exact Or.inr h
    case pos =>
      simp only [ne_eq, unitInterval.iteOneZero_eq_zero_def, not_and, Classical.not_imp,
        not_not] at h_sem
      rw [h_sem.right.right] at h
      simp only [wrtProg, Set.mem_empty_iff_false] at h
    case pos h_c' =>
      rw [h_c'] at h
      simp only [wrtProg, Set.mem_empty_iff_false] at h
    case neg =>
      split at h_sem
      case h_1 =>
        split_ifs at h_sem
        case pos => simp only [ne_eq, not_true_eq_false] at h_sem
        case pos h_c₂ =>
          simp only [wrtProg, Set.mem_union] at h
          cases h with
          | inl h => exact Or.inl (ih₁ h_sem h)
          | inr h => rw [h_c₂]; exact Or.inr h
        case neg => simp only [ne_eq, not_true_eq_false] at h_sem
      case h_2 => simp only [ne_eq, not_true_eq_false] at h_sem
  | concurrent c₁ c₂ ih₁ ih₂ =>
    simp only [wrtProg, Set.mem_union]
    rw [programSmallStepSemantics] at h_sem
    simp only at h_sem
    split_ifs at h_sem
    case pos =>
      simp only [ne_eq, unitInterval.iteOneZero_eq_zero_def, not_and, Classical.not_imp,
        not_not] at h_sem
      rw [h_sem.left] at h
      simp only [wrtProg, Set.mem_empty_iff_false] at h
    case pos =>
      simp only [ne_eq, unitInterval.iteOneZero_eq_zero_def, not_and, Classical.not_imp,
        not_not] at h_sem
      rw [h_sem.right.right] at h
      simp only [wrtProg, Set.mem_empty_iff_false] at h
    case pos h_c' =>
      rw [h_c'] at h
      simp only [wrtProg, Set.mem_empty_iff_false] at h
    case neg =>
      split at h_sem
      case h_1 =>
        split at h_sem
        case h_1 =>
          split_ifs at h_sem
          case pos => simp only [ne_eq, not_true_eq_false] at h_sem
          case pos h_c₂ =>
            simp only [wrtProg, Set.mem_union] at h
            cases h with
            | inl h => exact Or.inl (ih₁ h_sem h)
            | inr h => rw [h_c₂]; exact Or.inr h
          case neg => simp only [ne_eq, not_true_eq_false] at h_sem
        case h_2 => simp only [ne_eq, not_true_eq_false] at h_sem
      case h_2 =>
        split at h_sem
        case h_1 =>
          split_ifs at h_sem
          case pos => simp only [ne_eq, not_true_eq_false] at h_sem
          case pos h_c₁ =>
            simp only [wrtProg, Set.mem_union] at h
            cases h with
            | inl h => rw [h_c₁]; exact Or.inl h
            | inr h => exact Or.inr (ih₂ h_sem h)
          case neg => simp only [ne_eq, not_true_eq_false] at h_sem
        case h_2 => simp only [ne_eq, not_true_eq_false] at h_sem
      case h_3 => simp only [ne_eq, not_true_eq_false] at h_sem





end QSL
