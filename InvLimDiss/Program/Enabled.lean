import InvLimDiss.Program.Semantics

/-! This file features enabled actions. This is important as we do not want to take the
  infimum over non enabled actions, as we usually define them as 0.
  We could also set all non-enabled actions to 1 -- but this may be more confusing. -/

namespace Semantics

open Syntax Classical State Program unitInterval

variable {Variable : Type}

/-- The definition of enabled Action hard coded. -/
@[simp]
def enabledAction : (Program Variable) → (State Variable) → Set Action
  | [Prog| ↓], _                => ∅
  | [Prog| ↯], _                => ∅
  | [Prog| skip], _             => { Action.deterministic }
  | [Prog| _ ≔ _], _            => { Action.deterministic }
  | [Prog| _ *≔ _], _           => { Action.deterministic }
  | [Prog| _ ≔* _], _           => { Action.deterministic }
  | [Prog| _ ≔ cas(_, _, _)], _ => { Action.deterministic }
  | [Prog| _ ≔ alloc(e)], s     => if ∃ n : ℕ, n = e s.stack
    then { a | ∃ m, a = Action.allocation m ∧ ∃ n : ℕ, n = e s.stack ∧ isNotAlloc s.heap m n }
    else { Action.deterministic }
  | [Prog| free(_,_)], _        => { Action.deterministic }
  | [Prog| [[c₁]] ; [[_]]], s   => if c₁ = [Prog| ↓] then { Action.deterministic } else enabledAction c₁ s
  | [Prog| pif _ then [[_]] else [[_]] fi], _   => { Action.deterministic }
  | [Prog| if _ then [[_]] else [[_]] fi], _    => { Action.deterministic }
  | [Prog| while _ begin [[_]] fi], _           => { Action.deterministic }
  | [Prog| [[c₁]] || [[c₂]]], s
    => if c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] then { Action.deterministic } else
      { Action.concurrentLeft a | a ∈ enabledAction c₁ s } ∪ { Action.concurrentRight a | a ∈ enabledAction c₂ s }

/-- Disabled actions have trivial subdistributions. -/
theorem zero_probability_of_not_enabledAction
    {c : Program Variable} {s : State Variable} {a : Action}
    (h : ¬ a ∈ enabledAction c s) (c' : Program Variable) (s' : State Variable) :
    programSmallStepSemantics c s a c' s' = 0 := by

  induction c generalizing c' a with
  | terminated => simp only [programSmallStepSemantics, Pi.zero_apply]
  | error => simp only [programSmallStepSemantics, Pi.zero_apply]
  | skip' =>
    simp only [programSmallStepSemantics, skipSmallStepSemantics]
    rw[iteOneZero_neg]; simp only [not_and_or]; exact Or.inr <| Or.inl h
  | assign v e =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, assignSmallStepSemantics]
    split
    pick_goal 2; rfl
    rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h
  | manipulate e e' =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, manipulateSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
  | lookup v e =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, lookupSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
    | compareAndSet v e_l e_v e_n =>
      rw [enabledAction, Set.mem_singleton_iff] at h
      simp only [programSmallStepSemantics, compareAndSetSmallStepSemantics]
      split
      pick_goal 3; rfl
      all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
    | free' v n =>
      rw [enabledAction, Set.mem_singleton_iff] at h
      simp only [programSmallStepSemantics, freeSmallStepSemantics]
      split
      pick_goal 3; rfl
      all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
    | allocate v n =>
      simp only [enabledAction] at h
      split at h
      case isTrue h_n =>
        simp only [Set.mem_setOf_eq, not_exists, not_and] at h
        obtain ⟨n, h_n⟩ := h_n
        simp only [programSmallStepSemantics, allocateSmallStepSemantics, not_exists]
        split
        · simp only [iteOneZero_eq_zero_def, not_exists, not_and]
          rintro m h_m n' h_n' h_alloc _
          exact h m h_m n' h_n' h_alloc
        · simp only [iteOneZero_eq_zero_def, not_and, not_forall, Decidable.not_not]
          rintro rfl rfl
          use n
        · rfl
      case isFalse h_n =>
        simp only [programSmallStepSemantics, allocateSmallStepSemantics, not_exists]
        split
        · simp only [iteOneZero_eq_zero_def, not_exists, not_and]
          intro m _ n' h_n' _ _
          apply h_n
          use n'
        · simp only [iteOneZero_eq_zero_def, not_and, not_forall, Decidable.not_not]
          rintro rfl
          simp only [Set.mem_singleton_iff, not_true_eq_false] at h
        · rfl

  | probabilisticChoice e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
    simp only [ite_eq_right_iff, and_imp]
    intro h'; exfalso; exact h h'
  | conditionalChoice e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
    rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h
  | loop e c _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, loopSmallStepSemantics]
    split
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)

  | sequential c₁ c₂ ih₁ _ =>
    simp only [programSmallStepSemantics]
    split
    case isTrue h_term₁ =>
      obtain rfl := h_term₁
      rw [iteOneZero_eq_zero_def]
      rintro ⟨rfl, _⟩
      simp only [enabledAction, ↓reduceIte, Set.mem_singleton_iff, not_true_eq_false] at h
    case isFalse h_n_term₁ =>
      simp only [enabledAction, if_neg h_n_term₁] at h
      split
      case isTrue h_error' =>
        exact ih₁ h _
      case isFalse h_n_error' =>
        split
        case h_1 =>
          split
          case isTrue _ =>
            exact ih₁ h _
          case isFalse _ =>
            rfl
        case h_2 =>
          rfl

  | concurrent c₁ c₂ ih₁ ih₂ =>
    rw [enabledAction] at h
    split at h
    case isTrue h_term =>
      simp only [programSmallStepSemantics, h_term.left, h_term.right, and_self, ↓reduceIte]
      rw [iteOneZero_neg]
      simp only [not_and]
      intro _ h_a
      rw [Set.mem_singleton_iff] at h
      exact (h h_a).elim
    case isFalse h_term =>
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at h
      let ⟨h_left, h_right⟩ := h; clear h
      simp only [programSmallStepSemantics]
      split
      case isTrue h_term' => exact (h_term h_term').elim
      case isFalse =>
      split
      case h_1 a₂ a₁ =>
        have ha₁ : a₁ ∉ enabledAction c₁ s := by {
          intro h
          specialize h_left a₁ h
          simp only [not_true_eq_false] at h_left
        }
        split
        case isTrue h_error' =>
          exact ih₁ ha₁ _
        case isFalse h_n_error' =>
          split
          case h_1 =>
            simp only [ite_eq_right_iff]
            rintro rfl
            exact ih₁ ha₁ _
          case h_2 =>
            rfl
      case h_2 a₁ a₂ =>
        have ha₂ : a₂ ∉ enabledAction c₂ s := by {
          intro h
          specialize h_right a₂ h
          simp only [not_true_eq_false] at h_right
        }
        split
        case isTrue h_error' =>
          exact ih₂ ha₂ _
        case isFalse h_n_term' =>
          split
          case h_1 =>
            simp only [ite_eq_right_iff]
            rintro rfl
            exact ih₂ ha₂ _
          case h_2 =>
            rfl
      case h_3 => rfl

end Semantics
