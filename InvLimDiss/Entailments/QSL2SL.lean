import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.QuantitativeProofrules

/-
This file contains the transformation from (static) quantitative separation logic
into classical separation logic
-/

namespace Qsl2Sl

open unitInterval State QSL SL Syntax

variable {Var : Type}

def valuesOf (f : StateRV Var) : Set I := { x : I | ∃ s, f s = x}

theorem valuesOf_of_self {f : StateRV Var} {s : State Var} : f s ∈ valuesOf f := by
  unfold valuesOf; use s

theorem nonempty_valuesOf {f : StateRV Var} : Set.Nonempty (valuesOf f) := by
  have s : State Var := ⟨fun _ => 0, fun _ => HeapValue.undef⟩
  use (f s)
  exact valuesOf_of_self

theorem qsl_entail_if_at_least (f g : StateRV Var) {values : Set I} (h_subset : valuesOf f ⊆ values) :
    f ⊢ g ↔ ∀ i ∈ values, ∀ s, i ≤ f s → i ≤ g s := by
  apply Iff.intro
  · intro h i _ s h_f
    calc i
      _ ≤ f s := h_f
      _ ≤ g s := h s
  · intro h s
    refine h (f s) ?_ s (le_refl (f s))
    exact Set.mem_of_subset_of_mem h_subset valuesOf_of_self

theorem zero_le_atLeast (f : StateRV Var) (s : State Var) : 0 ≤ f s := nonneg'

theorem atLeast_qslEmp_iff {i : I} (h_lt : 0 < i) (s : State Var) :
    i ≤ `[qsl| emp] s ↔ `[sl| emp] s := by
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
    i ≤ `[qsl| l ↦ l'] s ↔ `[sl| l ↦ l'] s := by
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

theorem atLeast_qslReal_iff {i : I} {e : ProbExp Var} (s : State Var) :
    i ≤ `[qsl| <e>] s ↔ i ≤ (e s.stack) := ⟨fun h => h, fun h => h⟩

theorem atLeast_qslIverson_iff {i : I} (h_lt : 0 < i) (P : State Var → Prop) (s : State Var) :
    i ≤ `[qsl| ⁅P⁆] s ↔ P s := by
  unfold qslIverson
  apply Iff.intro
  · intro h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    rw [iteOneZero_pos h]
    exact le_one'

theorem atLeast_qslNot_of_slNot {i : I } {f : StateRV Var} {s : State Var} {values : Set I}
  (h_subset : valuesOf f ⊆ values) :
    `[sl| ¬ [[fun s => sInf {j ∈ values | σ i < j } ≤ f s]]] s → i ≤ `[qsl| ~[[f]]] s := by
  unfold slNot qslNot
  intro h
  rw [le_symm_iff_le_symm, ← not_lt]
  intro h_lt
  rw [not_le] at h
  apply (not_le_of_lt h)
  apply sInf_le
  apply And.intro
  · exact Set.mem_of_subset_of_mem h_subset valuesOf_of_self
  · exact h_lt

theorem lt_sInf_of_valuesOf {values : Set I} (h_fin : Set.Finite (values)) {i : I} (h_lt : 0 < i) :
    σ i < sInf {j ∈ values | σ i < j } := by
  have h_fin : Set.Finite {j ∈ values | σ i < j } := Set.Finite.subset h_fin (Set.sep_subset values (fun j => σ i < j))
  by_cases Set.Nonempty {j ∈ values | σ i < j }
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

theorem atLeast_qslNot_iff {i : I} {f : StateRV Var} {s : State Var} {values : Set I}
  (h_subset : valuesOf f ⊆ values) (h_min : σ i < sInf {j ∈ values | σ i < j }) :
    i ≤ `[qsl| ~[[f]]] s ↔ `[sl| ¬ [[fun s => sInf {j ∈ values | σ i < j } ≤ f s]]] s := by
  apply Iff.intro
  · unfold slNot qslNot
    intro h
    rw [not_le]
    rw [le_symm_iff_le_symm] at h
    apply lt_of_le_of_lt h; clear h
    exact h_min
  · exact atLeast_qslNot_of_slNot h_subset

theorem atLeast_qslMin_iff {i : I} {f₁ f₂ : StateRV Var} {s : State Var} :
    i ≤ `[qsl| [[f₁]] ⊓ [[f₂]]] s ↔ `[sl| [[fun s => i ≤ f₁ s]] ∧ [[fun s => i ≤ f₂ s]]] s := by
  rw [ qslMin, slAnd, Pi.inf_apply, Pi.inf_apply ]
  apply Iff.intro
  · intro h
    rw [inf_eq_min, min_def] at h
    split at h
    case inl h_le =>
      apply And.intro
      · exact h
      · exact le_trans h h_le
    case inr h_lt =>
      rw [not_le] at h_lt
      apply And.intro
      · exact le_of_lt <| lt_of_le_of_lt h h_lt
      · exact h
  · rintro ⟨h₁, h₂⟩
    rw [inf_eq_min, min_def]
    split
    case inl h_le => exact h₁
    case inr h_lt => exact h₂

theorem atLeast_qslMax_iff {i : I} {f₁ f₂ : StateRV Var} {s : State Var} :
    i ≤ `[qsl| [[f₁]] ⊔ [[f₂]]] s ↔ `[sl| [[fun s => i ≤ f₁ s]] ∨ [[fun s => i ≤ f₂ s]]] s := by
  rw [ qslMax, slOr, Pi.sup_apply, Pi.sup_apply ]
  apply Iff.intro
  · intro h
    rw [sup_eq_max, max_def] at h
    split at h
    case inl h_le =>
      apply Or.inr
      exact h
    case inr h_lt =>
      apply Or.inl
      rw [not_le] at h_lt
      exact h
  · rintro (h | h)
    · rw [sup_eq_max, max_def]
      split
      case inl h_le => refine le_trans h h_le
      case inr h_lt => exact h
    · rw [sup_eq_max, max_def]
      split
      case inl h_le => exact h
      case inr h_lt => rw [not_le] at h_lt; refine le_trans h (le_of_lt h_lt)

theorem atLeast_qslAdd_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : valuesOf f₁ ⊆ values₁) (h_subset₂ : valuesOf f₂ ⊆ values₂) :
    i ≤ `[qsl| [[f₁]] + [[f₂]]] s
    ↔ ∃ i₁ ∈ values₁, ∃ i₂ ∈ values₂, i ≤ (i₁:ℝ) + i₂ ∧ `[sl| [[fun s => i₁ ≤ f₁ s]] ∧ [[fun s => i₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    use (f₁ s), (Set.mem_of_subset_of_mem h_subset₁ valuesOf_of_self)
    use (f₂ s), (Set.mem_of_subset_of_mem h_subset₂ valuesOf_of_self)
    rw [ qslAdd, le_truncatedAdd] at h
    use h, le_rfl
  · rintro ⟨i₁, _, i₂, _, h_i, h₁, h₂⟩
    rw [ qslAdd, le_truncatedAdd]
    rw [ Subtype.mk_le_mk] at h₁ h₂
    calc (i:ℝ)
    _ ≤ (i₁:ℝ) + i₂ := h_i
    _ ≤ (f₁ s) + i₂ := add_le_add_right h₁ ↑i₂
    _ ≤ (f₁ s) + (f₂ s) := add_le_add_left h₂ (f₁ s)

theorem atLeast_qslMul_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : valuesOf f₁ ⊆ values₁) (h_subset₂ : valuesOf f₂ ⊆ values₂) :
    i ≤ `[qsl| [[f₁]] · [[f₂]]] s
    ↔ ∃ i₁ ∈ values₁, ∃ i₂ ∈ values₂, i ≤ i₁ * i₂ ∧ `[sl| [[fun s => i₁ ≤ f₁ s]] ∧ [[fun s => i₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    use (f₁ s), (Set.mem_of_subset_of_mem h_subset₁ valuesOf_of_self)
    use (f₂ s), (Set.mem_of_subset_of_mem h_subset₂ valuesOf_of_self)
    rw [ qslMul] at h
    use h, le_rfl
  · rintro ⟨i₁, _, i₂, _, h_i, h₁, h₂⟩
    rw [ qslMul ]
    calc i
    _ ≤ i₁ * i₂ := h_i
    _ ≤ (f₁ s) * i₂ := mul_le_mul_of_nonneg_right h₁ nonneg'
    _ ≤ (f₁ s) * (f₂ s) := mul_le_mul_of_nonneg_left h₂ nonneg'

theorem atLeast_qslSup_if {α : Type} { i : I } {f : α → StateRV Var} {s : State Var} :
    `[sl| ∃ x. [[fun s => i ≤ f x s]]] s → i ≤ `[qsl| S x. [[f x]]] s := by
  rw [qslSup_apply, slExists_apply ]
  rintro ⟨x, h⟩
  rw [le_sSup_iff]
  intro j hj
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hj
  calc i
  _ ≤ f x s := h
  _ ≤ j := hj x

theorem ex_max_of_finite_values_of_nonempty {α : Type} {f : α → StateRV Var} {s : State Var}
    (h_nonempty : Nonempty α) (h_finite : Set.Finite {i | ∃ x, f x s = i}) :
    ∃ x, ∀ y, f y s ≤ f x s := by
  have : sSup {i | ∃ x, f x s = i} ∈ {i | ∃ x, f x s = i} := by {
    apply Set.Nonempty.csSup_mem
    · have x := Classical.choice h_nonempty
      have : Set.Nonempty (valuesOf (f x)) := nonempty_valuesOf
      obtain ⟨i, _⟩ := this
      use (f x s), x
    · exact h_finite
  }
  obtain ⟨x, h⟩ := this
  use x
  intro y
  rw [h]
  apply le_sSup
  use y

theorem atLeast_qslSup_iff {α : Type} { i : I } {f : α → StateRV Var} {s : State Var}
    (h_max : ∃ x, ∀ y, f y s ≤ f x s) :
    i ≤ `[qsl| S x. [[f x]]] s ↔ `[sl| ∃ x. [[fun s => i ≤ f x s]]] s := by
  apply Iff.intro
  · rw [qslSup_apply, slExists_apply ]
    intro h
    rw [le_sSup_iff] at h
    obtain ⟨x, h_max⟩ := h_max
    use x
    apply h (f x s)
    simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
    intro y
    exact h_max y
  · exact atLeast_qslSup_if


theorem atLeast_qslInf_iff {α : Type} { i : I } {f : α → StateRV Var} {s : State Var} :
    i ≤ `[qsl| I x. [[f x]]] s ↔ `[sl| ∀ x. [[fun s => i ≤ f x s]]] s := by
  rw [qslInf_apply, slAll_apply ]
  apply Iff.intro
  · intro h x
    rw [le_sInf_iff] at h
    apply h (f x s)
    use x
  · rintro h
    rw [le_sInf_iff]
    rintro j ⟨x, hx⟩
    calc i
    _ ≤ f x s := h x
    _ = j := hx

theorem atLeast_qslSepMul_if { i : I } {f₁ f₂ : StateRV Var} {s : State Var} :
    (∃ j₁, ∃ j₂, i ≤ j₁ * j₂ ∧ `[sl| [[fun s => j₁ ≤ f₁ s]] ∗ [[fun s => j₂ ≤ f₂ s]]] s)
    → i ≤ `[qsl| [[f₁]] ⋆ [[f₂]]] s := by
  rintro ⟨j₁, j₂, hi_le, ⟨heap₁, heap₂, h₁, h₂, h_disjoint, h_union⟩⟩
  rw [qslSepMul, le_sSup_iff]
  rintro j h
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
  calc i
  _ ≤ j₁ * j₂ := hi_le
  _ ≤ (f₁ ⟨s.stack, heap₁⟩) * j₂ := mul_le_mul_of_nonneg_right h₁ nonneg'
  _ ≤ (f₁ ⟨s.stack, heap₁⟩) * (f₂ ⟨s.stack, heap₂⟩) := mul_le_mul_of_nonneg_left h₂ nonneg'
  _ ≤ j := (h heap₁ heap₂ h_disjoint h_union rfl)

theorem exists_heaps_max_of_finite_location {f₁ f₂ : StateRV Var} {s : State Var}
    (h_finite_domain : Set.Finite {loc | s.heap loc ≠ undef}):
    ∃ heap₁ heap₂, disjoint heap₁ heap₂ ∧ heap₁ ∪ heap₂ = s.heap
    ∧ f₁ ⟨s.stack, heap₁⟩ * f₂ ⟨s.stack, heap₂⟩ = `[qsl| [[f₁]] ⋆ [[f₂]]] s := by
  sorry

theorem atLeast_qslSepMul_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : valuesOf f₁ ⊆ values₁) (h_subset₂ : valuesOf f₂ ⊆ values₂)
    (h_max : ∃ heap₁ heap₂, disjoint heap₁ heap₂ ∧ heap₁ ∪ heap₂ = s.heap
      ∧ f₁ ⟨s.stack, heap₁⟩ * f₂ ⟨s.stack, heap₂⟩ = `[qsl| [[f₁]] ⋆ [[f₂]]] s) :
    i ≤ `[qsl| [[f₁]] ⋆ [[f₂]]] s
    ↔ ∃ j₁ ∈ values₁, ∃ j₂ ∈ values₂, i ≤ j₁ * j₂
      ∧ `[sl| [[fun s => j₁ ≤ f₁ s]] ∗ [[fun s => j₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    obtain ⟨heap₁, heap₂, h_disjoint, h_union, h_max⟩ := h_max
    rw [← h_max] at h; clear h_max
    use (f₁ ⟨s.stack, heap₁⟩), (Set.mem_of_subset_of_mem h_subset₁ valuesOf_of_self)
    use (f₂ ⟨s.stack, heap₂⟩), (Set.mem_of_subset_of_mem h_subset₂ valuesOf_of_self)
    use h, heap₁, heap₂
  · rintro ⟨j₁, _, j₂, _, h⟩
    apply atLeast_qslSepMul_if
    use j₁, j₂















end Qsl2Sl
