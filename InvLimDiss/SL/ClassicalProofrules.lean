import InvLimDiss.SL.Classical

namespace SL

variable {Var : Type}

theorem monotone_slSepCon {P₁ P₂ Q₁ Q₂ : StateProp Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
    `[sl| [[P₁]] ∗ [[Q₁]] ⊢ [[P₂]] ∗ [[Q₂]]] := by
  rintro ⟨s,heap⟩ ⟨heap_P, heap_Q, h_P₁, h_Q₁, h_disjoint, h_union⟩
  obtain h_P₂ := h_P ⟨s,heap_P⟩ h_P₁
  obtain h_Q₂ := h_Q ⟨s,heap_Q⟩ h_Q₁
  exact ⟨heap_P, heap_Q, h_P₂, h_Q₂, h_disjoint, h_union⟩

theorem monotone_slSepImp {P₁ P₂ Q₁ Q₂ : StateProp Var} (h_P : P₂ ⊢ P₁) (h_Q : Q₁ ⊢ Q₂) :
    `[sl| [[P₁]] -∗ [[Q₁]] ⊢ [[P₂]] -∗ [[Q₂]]] := by
  intro ⟨s,heap⟩ h heap_P h_disjoint h_P₂
  obtain h_P₁ := h_P ⟨s,heap_P⟩ h_P₂
  exact h_Q ⟨s,heap ∪ heap_P⟩ <| h heap_P h_disjoint h_P₁

-- adjointness of sepcon and sepimp
theorem le_slSepImp_iff_slSepCon_le (P₁ P₂ P₃ : StateProp Var) :
    `[sl| [[P₁]] ⊢ [[P₂]] -∗ [[P₃]]] ↔ `[sl| [[P₁]] ∗ [[P₂]] ⊢ [[P₃]]] := by
  apply Iff.intro
  case mp =>
    rintro h ⟨s,heap⟩ ⟨heap₁, heap₂, h_P₁, h_P₂, h_disjoint, h_union⟩
    rw [← h_union]
    exact h ⟨s, heap₁⟩ h_P₁ heap₂ h_disjoint h_P₂
  case mpr =>
    rintro h ⟨s,heap⟩ h_P₁ heap₂ h_disjoint h_P₂
    have : `[sl| [[P₁]] ∗ [[P₂]]] ⟨s,heap ∪ heap₂⟩ := by {exists heap, heap₂}
    exact h ⟨s,heap ∪ heap₂ ⟩ this

-- modus ponens of sepimp and sepcon
theorem slSepCon_slSepImp_entail (P₁ P₂ : StateProp Var) :
    `[sl| ([[P₁]] -∗ [[P₂]]) ∗ [[P₁]] ⊢ [[P₂]]] := by
  rintro ⟨s,heap⟩ ⟨heap₂, heap₁, h, h₁, h_disjoint, rfl⟩
  exact h heap₁ h_disjoint h₁

open State

theorem slExists_apply (P : α → StateProp Var) (s : State Var) :
    `[sl| ∃ x. [[P x]]] s ↔ ∃ x, P x s := by
  rw [slExists, sSup_apply, iSup, Set.range]
  simp only [eq_iff_iff, Subtype.exists, exists_prop, sSup_Prop_eq, Set.mem_setOf_eq]
  apply Iff.intro
  · rintro ⟨p, ⟨px, ⟨x, hx⟩, h⟩, hp⟩
    use x
    rw [hx, h]
    exact hp
  · rintro ⟨x, hp⟩
    use (P x s); refine And.intro ?_ hp
    use (P x); refine And.intro ?_ (Eq.to_iff rfl)
    use x

theorem slAll_apply (P : α → StateProp Var) (s : State Var) :
    `[sl| ∀ x. [[P x]]] s ↔ ∀ x, P x s := by
  rw [slAll, sInf_apply, iInf, Set.range]
  simp only [eq_iff_iff, Subtype.exists, exists_prop, sInf_Prop_eq, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
  apply Iff.intro
  · rintro h x
    specialize h (P x s) (P x)
    apply h
    · use x
    · exact Eq.to_iff rfl
  · intro h P' P'' ⟨x, hx⟩ hP'
    rw [← hP', ← hx]
    exact h x

end SL
