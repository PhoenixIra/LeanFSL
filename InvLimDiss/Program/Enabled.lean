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
  | [Prog| pif _ then [[_]] else [[_]] fi], _   => { Action.deterministic }
  | [Prog| if _ then [[_]] else [[_]] fi], _    => { Action.deterministic }
  | [Prog| while _ begin [[_]] fi], _           => { Action.deterministic }
  | [Prog| [[c₁]] ; [[_]]], s   => if c₁ = [Prog| ↓] ∨ c₁ = [Prog| ↯]
      then { Action.deterministic } else enabledAction c₁ s
  | [Prog| [[c₁]] || [[c₂]]], s
    => if (c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓]) ∨ c₁ = [Prog| ↯] ∨ c₂ = [Prog| ↯]
      then { Action.deterministic } else
      { Action.concurrentLeft a | a ∈ enabledAction c₁ s }
      ∪ { Action.concurrentRight a | a ∈ enabledAction c₂ s }

/-- Disabled actions have trivial subdistributions. -/
theorem zero_probability_of_not_enabledAction
    {c : Program Variable} {s : State Variable} {a : Action}
    (h : ¬ a ∈ enabledAction c s) (c' : Program Variable) (s' : State Variable) :
    programSmallStepSemantics c s a c' s' = 0 := by

  induction c generalizing c' a with
  | terminated => simp only [programSmallStepSemantics, Pi.zero_apply]
  | abort => simp only [programSmallStepSemantics, Pi.zero_apply]
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

  | probabilisticBranching e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, probabilisticBranchingSmallStepSemantics]
    simp only [ite_eq_right_iff, and_imp]
    intro h'; exfalso; exact h h'
  | conditionalBranching e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, conditionalBranchingSmallStepSemantics]
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
      simp only [enabledAction, or_false, ↓reduceIte, Set.mem_singleton_iff, not_true_eq_false] at h
    case isFalse h_n_term =>
      simp only [enabledAction, if_neg h_n_term] at h
      split
      case isTrue h_abort =>
        obtain rfl := h_abort
        simp only [iteOneZero_eq_zero_def, not_and]
        intro ha _ _
        simp only [or_true, ↓reduceIte, Set.mem_singleton_iff] at h
        exact h ha
      case isFalse h_n_abort =>
        split
        case isTrue h_c' =>
          obtain rfl := h_c'
          rw [if_neg] at h
          · exact ih₁ h [Prog|↯]
          · rintro (rfl | rfl)
            · simp only [not_true_eq_false] at h_n_term
            · simp only [not_true_eq_false] at h_n_abort
        case isFalse h_c' =>
          split
          case h_1 =>
            split
            case isTrue _ => rfl
            case isFalse _ =>
              split
              case isTrue _ =>
                rw [if_neg] at h
                · exact ih₁ h _
                · rintro (rfl | rfl)
                  · simp only [not_true_eq_false] at h_n_term
                  · simp only [not_true_eq_false] at h_n_abort
              case isFalse _ => rfl
          case h_2 =>
            rfl

  | concurrent c₁ c₂ ih₁ ih₂ =>
    rw [enabledAction] at h
    split at h
    simp only [Set.mem_singleton_iff] at h
    case isTrue h_c =>
      cases h_c with
      | inl h_term =>
        simp only [programSmallStepSemantics, h_term.left, h_term.right, and_self, ↓reduceIte,
          iteOneZero_eq_zero_def, not_and]
        rintro _ rfl
        simp only [Set.mem_singleton_iff, not_true_eq_false] at h
      | inr h_abort =>
        cases h_abort with
        | inl h_c₁ =>
          obtain rfl := h_c₁
          simp only [programSmallStepSemantics, false_and, ↓reduceIte, true_or,
            iteOneZero_eq_zero_def, not_and]
          intro ha _ _
          exact h ha
        | inr h_c₂ =>
          obtain rfl := h_c₂
          simp only [programSmallStepSemantics, and_false, ↓reduceIte, or_true,
            iteOneZero_eq_zero_def, not_and]
          intro ha _ _
          exact h ha
    case isFalse h_c =>
      simp only [not_or, not_and] at h_c
      obtain ⟨h_term, h_c₁_n_abort, h_c₂_n_abort⟩ := h_c
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at h
      obtain ⟨h_left, h_right⟩ := h
      simp only [programSmallStepSemantics]
      split
      case isTrue h_term' =>
        exfalso
        exact h_term h_term'.left h_term'.right
      case isFalse =>
        split
        case isTrue h_term' h_abort =>
          exfalso
          cases h_abort with
          | inl h_c₁ => exact h_c₁_n_abort h_c₁
          | inr h_c₂ => exact h_c₂_n_abort h_c₂
        case isFalse h_term' h_abort =>
          split
          case h_1 a₂ a₁ =>
            have ha₁ : a₁ ∉ enabledAction c₁ s := by {
              intro h
              specialize h_left a₁ h
              simp only [not_true_eq_false] at h_left
            }
            split
            case isTrue h_abort =>
              exact ih₁ ha₁ _
            case isFalse h_ne_abort =>
              split
              case h_1 =>
                split
                case isTrue => rfl
                case isFalse =>
                  simp only [ite_eq_right_iff]
                  intro _
                  exact ih₁ ha₁ _
              case h_2 => rfl
          case h_2 a₁ a₂ =>
            have ha₂ : a₂ ∉ enabledAction c₂ s := by {
              intro h
              specialize h_right a₂ h
              simp only [not_true_eq_false] at h_right
            }
            split
            case isTrue h_abort =>
              exact ih₂ ha₂ _
            case isFalse h_ne_abort =>
              split
              case h_1 =>
                split
                case isTrue => rfl
                case isFalse =>
                  simp only [ite_eq_right_iff]
                  rintro _
                  exact ih₂ ha₂ _
              case h_2 => rfl
          case h_3 => rfl

end Semantics
