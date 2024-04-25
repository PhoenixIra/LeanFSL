import InvLimDiss.Program.Semantics

namespace Semantics

open Syntax Classical State Program unitInterval

variable {Variable : Type}

def enabledAction : (Program Variable) → (State Variable) → Set Action
  | `[Prog| ↓], _                => ∅
  | `[Prog| ↯], _                => ∅
  | `[Prog| skip], _             => { Action.deterministic }
  | `[Prog| _ ≔ _], _            => { Action.deterministic }
  | `[Prog| _ *≔ _], _           => { Action.deterministic }
  | `[Prog| _ ≔* _], _           => { Action.deterministic }
  | `[Prog| _ ≔ cas(_, _, _)], _ => { Action.deterministic }
  | `[Prog| _ ≔ alloc(n)], s     => { a | ∃ m, a = Action.allocation m ∧ isNotAlloc s m n }
  | `[Prog| free(_,_)], _        => { Action.deterministic }
  | `[Prog| [[c₁]] ; [[_]]], s   => if c₁ = `[Prog| ↓] then { Action.deterministic } else enabledAction c₁ s
  | `[Prog| pif _ then [[_]] else [[_]] end], _   => { Action.deterministic }
  | `[Prog| if _ then [[_]] else [[_]] end], _    => { Action.deterministic }
  | `[Prog| while _ begin [[_]] end], _           => { Action.deterministic }
  | `[Prog| [[c₁]] || [[c₂]]], s
    => if c₁ = `[Prog| ↓] ∧ c₂ = `[Prog| ↓] then { Action.deterministic } else
      { Action.concurrentLeft a | a ∈ enabledAction c₁ s } ∪ { Action.concurrentRight a | a ∈ enabledAction c₂ s }

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
      simp only [enabledAction, Set.mem_setOf_eq, not_exists, not_and] at h
      simp only [programSmallStepSemantics, allocateSmallStepSemantics]
      rw [iteOneZero_neg]
      simp only [not_exists, not_and]
      intro _ x h_act h_nalloc
      exfalso
      exact h x h_act h_nalloc

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
    cases eq_or_ne c₁ `[Prog| ↓] with
    | inl h_eq =>
      simp only [programSmallStepSemantics, h_eq]
      rw [iteOneZero_neg]; simp only [↓reduceIte]
      rw [h_eq, enabledAction] at h; simp only [↓reduceIte, Set.mem_singleton_iff] at h
      rintro ⟨h_a, _⟩
      exact h h_a
    | inr h_ne =>
      rw [enabledAction, if_neg h_ne] at h
      specialize ih₁ h
      simp only [programSmallStepSemantics]
      split
      case inl h_term => exact (h_ne h_term).elim
      case inr _ =>
        split
        case h_1 h_term _ c₁' c₂' =>
          split
          case inl h_c₁ => exact ih₁ c₁'
          case inr h_c₁ => rfl
        case h_2 _ => rfl

  | concurrent c₁ c₂ ih₁ ih₂ =>
    rw [enabledAction] at h
    split at h
    case inl h_term =>
      simp only [programSmallStepSemantics, h_term.left, h_term.right, and_self, ↓reduceIte]
      rw [iteOneZero_neg]
      simp only [not_and]
      intro _ h_a
      rw [Set.mem_singleton_iff] at h
      exact (h h_a).elim
    case inr h_term =>
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at h
      let ⟨h_left, h_right⟩ := h; clear h
      simp only [programSmallStepSemantics]
      split
      case inl h_term' => exact (h_term h_term').elim
      case inr _ =>
      split
      case h_1 _ c₁' c₂' =>
        split
        case h_1 _ a =>
          split
          case inl h_c₂ =>
            have : a ∉ enabledAction c₁ s := by {
              intro h
              specialize h_left a h
              simp only [not_true_eq_false] at h_left
            }
            exact ih₁ this c₁'
          case inr => rfl
        case h_2 _ a =>
          split
          case inl h_c₂ =>
            have : a ∉ enabledAction c₂ s := by {
              intro h
              specialize h_right a h
              simp only [not_true_eq_false] at h_right
            }
            exact ih₂ this c₂'
          case inr _ => rfl
        case h_3 _ _ _ => rfl
      case h_2 => rfl

end Semantics
