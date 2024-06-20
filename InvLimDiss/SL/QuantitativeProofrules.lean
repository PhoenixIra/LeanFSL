import InvLimDiss.SL.Quantitative

namespace QSL

open unitInterval State

variable {Var : Type}

theorem monotone_qslSepCon {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
    `[qsl Var| [[P₁]] ⋆ [[Q₁]] ⊢ [[P₂]] ⋆ [[Q₂]]] := by
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
    `[qsl| [[P₁]] -⋆ [[Q₁]] ⊢ [[P₂]] -⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply le_sInf
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ h_disjoint rfl
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro _ h
  specialize h heap₁ h_disjoint rfl
  apply le_trans h
  apply unit_div_le_div
  · exact h_Q ⟨s,heap ∪ heap₁⟩
  · exact h_P ⟨s,heap₁⟩

-- adjointness of sepcon and sepimp
theorem le_qslSepImp_iff_qslSepCon_le (P₁ P₂ P₃ : StateRV Var) :
    `[qsl| [[P₁]] ⊢ [[P₂]] -⋆ [[P₃]]] ↔ `[qsl| [[P₁]] ⋆ [[P₂]] ⊢ [[P₃]]] := by
  apply Iff.intro
  case mp =>
    intro h ⟨s,heap⟩
    apply sSup_le
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₁ heap₂ h_disjoint rfl rfl
    cases eq_or_ne (P₂ ⟨s,heap₂⟩) 0 with
    | inl h_eq => rw [h_eq, mul_zero]; exact nonneg'
    | inr h_ne =>
      rw [← (unit_le_div_iff_mul_le)]
      specialize h ⟨s,heap₁⟩
      unfold qslSepDiv at h
      simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
      exact h (P₃ ⟨s,heap₁ ∪ heap₂⟩ / P₂ ⟨s,heap₂⟩) heap₂ h_disjoint rfl
  case mpr =>
    intro h ⟨s,heap₁⟩
    apply le_sInf
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₂ h_disjoint rfl
    rw [unit_le_div_iff_mul_le]
    specialize h ⟨s,heap₁ ∪ heap₂⟩
    unfold qslSepMul at h
    rw [sSup_le_iff] at h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h (P₁ ⟨s,heap₁⟩ * P₂ ⟨s,heap₂⟩) heap₁ heap₂ h_disjoint rfl rfl

-- modus ponens of sepimp and sepcon
theorem qslSepCon_qslSepImp_entail (P₁ P₂ : StateRV Var) :
    `[qsl| ([[P₁]] -⋆ [[P₂]]) ⋆ [[P₁]] ⊢ [[P₂]]] := by
  rintro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  cases eq_or_ne (P₁ ⟨s, heap₂⟩) 0
  case inl h_eq =>
    rw [h_eq, mul_zero]
    exact nonneg'
  case inr h_ne =>
    rw [← unit_le_div_iff_mul_le]
    apply sInf_le
    simp only [Set.mem_setOf_eq]
    exists heap₂

theorem qslSup_apply (P : α → StateRV Var) (s : State Var) :
    `[qsl| S x. [[P x]]] s = sSup {y | ∃ x, P x s = y} := by
  rw [qslSup, sSup_apply, iSup, Set.range]
  simp only [Subtype.exists, exists_prop]
  apply le_antisymm
  · apply sSup_le_sSup
    rintro i ⟨P', ⟨⟨x, hx⟩, hP'⟩⟩
    use x
    rw [hx, hP']
  · apply sSup_le_sSup
    rintro i ⟨x, hx⟩
    use (P x)
    refine And.intro ?_ hx
    use x

theorem qslInf_apply (P : α → StateRV Var) (s : State Var) :
    `[qsl| I x. [[P x]]] s = sInf {y | ∃ x, P x s = y} := by
  rw [qslInf, sInf_apply, iInf, Set.range]
  simp only [Subtype.exists, exists_prop]
  apply le_antisymm
  · apply sInf_le_sInf
    intro i ⟨x, hx⟩
    use (P x)
    refine And.intro ?_ hx
    use x
  · apply sInf_le_sInf
    intro i ⟨P', ⟨⟨x, hx⟩, hP'⟩⟩
    use x
    rw [hx, hP']

theorem qslSepInv_eq_one (f₁ f₂ : StateRV Var) (s : State Var) :
    `[qsl| [[f₁]] -⋆ [[f₂]]] s = 1 ↔
    ∀ heap, disjoint s.heap heap →
      f₁ ⟨s.stack, heap⟩ ≤ f₂ ⟨s.stack, s.heap ∪ heap⟩ := by
  apply Iff.intro
  · intro h heap h_disjoint
    rw [← unit_div_eq_one_iff]
    apply le_antisymm le_one'
    rw [qslSepDiv] at h
    obtain h_inf := le_of_eq h.symm; clear h
    rw [le_sInf_iff] at h_inf
    specialize h_inf (f₂ ⟨s.stack, s.heap ∪ heap⟩ / f₁ ⟨s.stack, heap⟩)
    apply h_inf
    use heap
  · intro h
    conv at h => intro a b; rw [← unit_div_eq_one_iff]
    rw [qslSepDiv]
    apply le_antisymm le_one'
    apply le_sInf
    rintro i ⟨heap, h_disjoint, rfl⟩
    rw [h heap h_disjoint]

end QSL
