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
