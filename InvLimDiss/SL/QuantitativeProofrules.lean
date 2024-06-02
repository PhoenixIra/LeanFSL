import InvLimDiss.SL.Quantitative

namespace QSL

open unitInterval

variable {Var : Type}

theorem monotone_qslSepCon {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
    [qsl Var| [[P₁]] ⋆ [[Q₁]] ⊢ [[P₂]] ⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  apply le_sSup_iff.mpr
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro i h
  specialize h heap₁ heap₂ h_disjoint rfl rfl
  refine le_trans ?_ h; clear h
  apply mul_le_mul
  · exact h_P ⟨s,heap₁⟩
  · exact h_Q ⟨s,heap₂⟩
  · exact nonneg'
  · exact nonneg'

theorem monotone_qslSepImp {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₂ ⊢ P₁) (h_Q : Q₁ ⊢ Q₂) :
    [qsl| [[P₁]] -⋆ [[Q₁]] ⊢ [[P₂]] -⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply le_sInf
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ h_disjoint h_non_one rfl
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro _ h
  have := lt_of_lt_of_le h_non_one (h_P ⟨s,heap₁⟩)
  specialize h heap₁ h_disjoint this rfl; clear this
  apply le_trans h
  apply unit_div_le_div
  · exact h_non_one
  · exact h_Q ⟨s,heap ∪ heap₁⟩
  · exact h_P ⟨s,heap₁⟩

-- adjointness of sepcon and sepimp
theorem le_qslSepImp_iff_qslSepCon_le (P₁ P₂ P₃ : StateRV Var) :
    [qsl| [[P₁]] ⊢ [[P₂]] -⋆ [[P₃]]] ↔ [qsl| [[P₁]] ⋆ [[P₂]] ⊢ [[P₃]]] := by
  apply Iff.intro
  case mp =>
    intro h ⟨s,heap⟩
    apply sSup_le
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₁ heap₂ h_disjoint rfl rfl
    cases eq_or_ne (P₂ ⟨s,heap₂⟩) 0 with
    | inl h_eq => rw [h_eq, mul_zero]; exact nonneg'
    | inr h_ne =>
      have := lt_of_le_of_ne nonneg' h_ne.symm
      rw [← (unit_le_div_iff_mul_le _ _ _ this)]
      specialize h ⟨s,heap₁⟩
      unfold qslSepDiv at h
      simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
      exact h (P₃ ⟨s,heap₁ ∪ heap₂⟩ / P₂ ⟨s,heap₂⟩) heap₂ h_disjoint this rfl
  case mpr =>
    intro h ⟨s,heap₁⟩
    apply le_sInf
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₂ h_disjoint h_non_one rfl
    rw [unit_le_div_iff_mul_le _ _ _ h_non_one]
    specialize h ⟨s,heap₁ ∪ heap₂⟩
    unfold qslSepMul at h
    rw [sSup_le_iff] at h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h (P₁ ⟨s,heap₁⟩ * P₂ ⟨s,heap₂⟩) heap₁ heap₂ h_disjoint rfl rfl

-- modus ponens of sepimp and sepcon
theorem qslSepCon_qslSepImp_entail (P₁ P₂ : StateRV Var) :
    [qsl| ([[P₁]] -⋆ [[P₂]]) ⋆ [[P₁]] ⊢ [[P₂]]] := by
  rintro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  cases eq_or_ne (P₁ ⟨s, heap₂⟩) 0
  case inl h_eq =>
    rw [h_eq, mul_zero]
    exact nonneg'
  case inr h_ne =>
    have h_le := (lt_of_le_of_ne nonneg' (Ne.symm h_ne))
    rw [← unit_le_div_iff_mul_le _ _ _ h_le]
    apply sInf_le
    simp only [Set.mem_setOf_eq]
    exists heap₂





end QSL
