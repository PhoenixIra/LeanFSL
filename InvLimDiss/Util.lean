
theorem not_none_option_of_some_option (o : Option α) (a : α) (h : o = some a) : o ≠ none := by
  intro h_none
  cases o with
  | none => simp only at h
  | some a' => simp only at h_none

theorem none_option_iff_exists_option : (∃ a, o = some a) ↔ o ≠ none := by
  apply Iff.intro
  · intro ⟨a, h_a⟩
    rw [h_a]
    simp only [ne_eq, not_false_eq_true]
  · intro h
    cases o with
    | none => exfalso; exact h rfl
    | some b => exact Option.isSome_iff_exists.mp rfl


theorem ite_def {p : Prop} [dec : Decidable p] : (if p then a else b) = c ↔ p ∧ a = c ∨ ¬ p ∧ b = c := by
  apply Iff.intro
  · intro h
    cases dec with
    | isTrue h_p =>
      rw [if_pos h_p] at h
      exact Or.inl ⟨h_p, h⟩
    | isFalse h_np =>
      rw [if_neg h_np] at h
      exact Or.inr ⟨h_np, h⟩
  · intro h
    cases h with
    | inl h_p =>
      rw [if_pos h_p.left]
      exact h_p.right
    | inr h_np =>
      rw [if_neg h_np.left]
      exact h_np.right
