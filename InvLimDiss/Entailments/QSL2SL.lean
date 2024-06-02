import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.QuantitativeProofrules

/-
This file contains the transformation from (static) quantitative separation logic
into classical separation logic
-/

namespace Qsl2Sl

open unitInterval State QSL SL

variable {Var : Type}

def valuesOf (f : StateRV Var) : Set I := { x : I | ∃ s, f s = x}

theorem valuesOf_of_self {f : StateRV Var} {s : State Var} : f s ∈ valuesOf f := by
  unfold valuesOf; use s

theorem nonempty_valuesOf {f : StateRV Var} : Set.Nonempty (valuesOf f) := by
  have s : State Var := ⟨fun _ => 0, fun _ => HeapValue.undef⟩
  use (f s)
  exact valuesOf_of_self

theorem qsl_entail_if_at_least (f g : StateRV Var) : f ⊢ g ↔ ∀ i ∈ valuesOf f, ∀ s, i ≤ f s → i ≤ g s := by
  apply Iff.intro
  · intro h i _ s h_f
    calc i
      _ ≤ f s := h_f
      _ ≤ g s := h s
  · intro h s
    apply h (f s) valuesOf_of_self s (le_refl (f s))

theorem zero_le_atLeast (f : StateRV Var) (s : State Var) : 0 ≤ f s := nonneg'

theorem atLeast_qslEmp_iff {i : I} (h_lt : 0 < i) (s : State Var) :
    i ≤ [qsl| emp] s ↔ [sl| emp] s := by
  apply Iff.intro
  · intro h
    unfold slEmp
    split
    unfold qslEmp at h
    simp only at h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    unfold qslEmp
    split
    unfold slEmp at h
    simp only at h
    rw [iteOneZero_eq_one_def.mpr h]
    exact le_one'

theorem atLeast_qslPointsTo_iff {i : I} (h_lt : 0 < i) (s : State Var) :
    i ≤ [qsl| l ↦ l'] s ↔ [sl| l ↦ l'] s := by
  unfold slPointsTo qslPointsTo
  apply Iff.intro
  · intro h
    split
    simp only at h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    simp only at h
    rw [iteOneZero_eq_one_def.mpr h]
    exact le_one'

theorem atLeast_qslReal_iff {i j : I} (s : State Var) :
    i ≤ [qsl| <j>] s ↔ i ≤ j := ⟨fun h => h, fun h => h⟩

theorem atLeast_qslIverson_iff {i : I} (h_lt : 0 < i) (P : State Var → Prop) (s : State Var) :
    i ≤ [qsl| ⁅P⁆] s ↔ P s := by
  unfold qslIverson
  apply Iff.intro
  · intro h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    rw [iteOneZero_pos h]
    exact le_one'

theorem atLeast_qslNot_of_slNot {i : I } {f : StateRV Var} {P : StateProp Var} {s : State Var}
  (h_rec : sInf {j ∈ valuesOf f | σ i < j } ≤ f s ↔ P s)  :
    [sl| ¬ [[P]]] s → i ≤ [qsl| ~[[f]]] s := by
  unfold slNot qslNot
  intro h
  rw [le_symm_iff_le_symm, ← not_lt]
  intro h_lt
  rw [← h_rec, not_le] at h
  apply (not_le_of_lt h)
  apply sInf_le
  apply And.intro
  · simp only [valuesOf, Set.mem_setOf_eq, exists_apply_eq_apply]
  · exact h_lt

theorem lt_sInf_of_valuesOf (h_fin : Set.Finite (valuesOf f)) {i : I} (h_lt : 0 < i) :
    σ i < sInf {j ∈ valuesOf f | σ i < j } := by
  have h_fin : Set.Finite {j ∈ valuesOf f | σ i < j } := Set.Finite.subset h_fin (Set.sep_subset (valuesOf f) (fun j => σ i < j))
  by_cases Set.Nonempty {j ∈ valuesOf f | σ i < j }
  case neg h_empty =>
    rw [← unitInterval.symm_one, symm_lt_iff_symm_lt] at h_lt
    apply lt_of_lt_of_le h_lt
    apply le_sInf
    intro j h_j
    exact (h_empty ⟨j, h_j⟩).elim
  case pos h_nonempty =>
    rw [lt_iff_le_and_ne]
    apply And.intro
    · apply le_sInf
      rintro j ⟨_, h_lt⟩
      exact le_of_lt h_lt
    · intro h
      have h_mem := Set.Nonempty.csInf_mem h_nonempty h_fin
      rw [← h] at h_mem
      clear h_nonempty h_fin h
      simp only [Set.mem_setOf_eq, lt_self_iff_false, and_false] at h_mem

theorem atLeast_qslNot_iff {i : I} {f : StateRV Var} {P : StateProp Var} {s : State Var}
  (h_min : σ i < sInf {j ∈ valuesOf f | σ i < j })
  (h_rec : sInf {j ∈ valuesOf f | σ i < j } ≤ f s ↔ P s)  :
    i ≤ [qsl| ~[[f]]] s ↔ [sl| ¬ [[P]]] s := by
  apply Iff.intro
  · unfold slNot qslNot
    intro h
    rw [← h_rec, not_le]; clear h_rec
    rw [le_symm_iff_le_symm] at h
    apply lt_of_le_of_lt h; clear h
    exact h_min
  · exact atLeast_qslNot_of_slNot h_rec

theorem atLeast_qslMin_iff {i : I} {f₁ f₂ : StateRV Var} {P₁ P₂ : StateProp Var} {s : State Var}
  (h_rec₁ : i ≤ f₁ s ↔ P₁ s) (h_rec₂ : i ≤ f₂ s ↔ P₂ s) :
    i ≤ [qsl| [[f₁]] ⊓ [[f₂]]] s ↔ [sl| [[P₁]] ∧ [[P₂]]] s := by
  rw [ qslMin, slAnd, Pi.inf_apply, Pi.inf_apply ]
  apply Iff.intro
  · intro h
    rw [inf_eq_min, min_def] at h
    split at h
    case inl h_le =>
      apply And.intro
      · rw [← h_rec₁]
        exact h
      · rw [← h_rec₂]
        exact le_trans h h_le
    case inr h_lt =>
      rw [not_le] at h_lt
      apply And.intro
      · rw [← h_rec₁]
        exact le_of_lt <| lt_of_le_of_lt h h_lt
      · rw [← h_rec₂]
        exact h
  · intro h
    rw [inf_eq_min, min_def]
    split
    case inl h_le => sorry
    case inr h_lt => sorry





end Qsl2Sl
