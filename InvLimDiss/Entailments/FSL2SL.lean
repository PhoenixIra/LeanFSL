import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.Program.State.Finite
import Mathlib.Data.Set.Pointwise.Finite

/-!
This file contains the transformation from (static) quantitative separation logic
into classical separation logic. We try to use the least number of additional assumptions
and offer lemmas helping to prove this assumptions which require finiteness of the image.
We also provide overapproximation of the image to allow easy proving of the finiteness
of the image.
-/

namespace Qsl2Sl

open unitInterval State FSL SL Syntax Finite

variable {Var : Type}

/-- Sets of fsl RVs with exisential quantifiers are nonempty if the
  quantified type is nonempty. -/
theorem nonempty_StateRV_set {α : Type} (f : α → StateRV Var) (s : State Var)
    (h_nonempty : Nonempty α) : Set.Nonempty { i | ∃ x, f x s = i} := by
  let x := Classical.choice h_nonempty
  use (f x s), x

/-- The supremum is reached if the image is finite and the type is nonempty. -/
theorem sSup_mem_of_nonempty {α : Type} {f : α → StateRV Var} {s : State Var}
    (h_nonempty : Nonempty α) (h_finite : Set.Finite {i | ∃ x, f x s = i}) :
    sSup {i | ∃ y, f y s = i} ∈ {i | ∃ y, f y s = i} :=
  Set.Nonempty.csSup_mem (nonempty_StateRV_set f s h_nonempty) h_finite

/-- The supremum is inside of its closure. -/
lemma sSup_in_closure_of_subset (s s' : Set I) (h_nonempty : Set.Nonempty s) (h : s ⊆ s') :
    sSup s ∈ closure s' := by
  apply Set.mem_of_subset_of_mem (closure_mono h)
  exact sSup_mem_closure h_nonempty

/-- The infimum is reached if the image is finite and the type is nonempty. -/
theorem sInf_mem_of_nonempty {α : Type} {f : α → StateRV Var} {s : State Var}
    (h_nonempty : Nonempty α) (h_finite : Set.Finite {i | ∃ x, f x s = i}) :
    sInf {i | ∃ y, f y s = i} ∈ {i | ∃ y, f y s = i} :=
  Set.Nonempty.csInf_mem (nonempty_StateRV_set f s h_nonempty) h_finite

/-- The infimum is inside of its closure. -/
lemma sInf_in_closure_of_subset (s s' : Set I) (h_nonempty : Set.Nonempty s) (h : s ⊆ s') :
    sInf s ∈ closure s' := by
  apply Set.mem_of_subset_of_mem (closure_mono h)
  exact sInf_mem_closure h_nonempty

/-- The negation infimum is not its limit if the image is finite. -/
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

/-- The separating mulitiplication is realized if the heap is finite. -/
theorem exists_heaps_max_of_finite_heap {f₁ f₂ : StateRV Var} {s : State Var}
    (h_finite : Heap.Finite s.heap):
    `[fsl| [[f₁]] ⋆ [[f₂]]] s ∈ { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = s.heap
    ∧ x = f₁ ⟨s.stack, h₁⟩ * f₂ ⟨s.stack, h₂⟩} := by
  rw [fslSepMul]
  apply Set.Nonempty.csSup_mem
  · use (f₁ ⟨s.stack,∅⟩ * f₂ s), ∅, s.heap, emptyHeap_disjoint', emptyHeap_union'
  · apply Set.Finite.subset
    · have : Set.Finite {heap | ∃ heap', disjoint heap heap' ∧ heap ∪ heap' = s.heap} := by {
        apply Set.Finite.subset (Finite.finite_of_subheaps h_finite)
        intro heap ⟨heap', _, h_union⟩
        use heap'
      }
      apply Set.Finite.mul
      · exact Set.Finite.image (fun heap => f₁ ⟨s.stack,heap⟩) this
      · exact Set.Finite.image (fun heap => f₂ ⟨s.stack,heap⟩) this
    · intro i ⟨heap₁, heap₂, h_disjoint, h_union, h⟩
      rw [Set.mem_mul]
      use (f₁ ⟨s.stack,heap₁⟩)
      apply And.intro (by use heap₁; refine And.intro ?_ rfl; use heap₂)
      use (f₂ ⟨s.stack,heap₂⟩)
      refine And.intro ?_ h.symm
      use heap₂
      refine And.intro ?_ rfl
      use heap₁
      rw [disjoint_comm heap₂ heap₁, union_comm heap₂ heap₁ h_disjoint.symm]
      trivial

/-- The separating mulitiplication is realized if image is finite -/
theorem exists_fslSepMul_max_of_finite_values {f₁ f₂ : StateRV Var} (s : State Var)
    (h_finite₁ : Set.Finite (Set.range f₁)) (h_finite₂ : Set.Finite (Set.range f₂)):
    `[fsl| [[f₁]] ⋆ [[f₂]]] s ∈ { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = s.heap
    ∧ x = f₁ ⟨s.stack, h₁⟩ * f₂ ⟨s.stack, h₂⟩} := by
  rw [fslSepMul]
  apply Set.Nonempty.csSup_mem
  · use (f₁ ⟨s.stack,∅⟩ * f₂ s), ∅, s.heap, emptyHeap_disjoint', emptyHeap_union'
  · apply Set.Finite.subset (Set.Finite.mul h_finite₁ h_finite₂)
    rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
    simp only [Set.mem_mul]
    use (f₁ ⟨s.stack, heap₁⟩), (Set.mem_range_self _), (f₂ ⟨s.stack, heap₂⟩), (Set.mem_range_self _)

/-- The separating division is realized if image is finite -/
theorem exists_fslSepDiv_min_of_finite_values {f₁ f₂ : StateRV Var} (s : State Var)
    (h_finite₁ : Set.Finite (Set.range f₁)) (h_finite₂ : Set.Finite (Set.range f₂)) :
    `[fsl| [[f₁]] -⋆ [[f₂]]] s ∈ { x | ∃ heap, disjoint s.heap heap
      ∧ x = f₂ ⟨s.stack, s.heap ∪ heap⟩ / f₁ ⟨s.stack, heap⟩} := by
  rw [fslSepDiv]
  apply Set.Nonempty.csInf_mem
  · use ((f₂ s) / (f₁ ⟨s.stack, ∅⟩)), ∅, disjoint_emptyHeap'
    rw [union_emptyHeap']
  · apply Set.Finite.subset (Set.Finite.image2 Div.div h_finite₂ h_finite₁)
    rintro _ ⟨heap, _, rfl⟩
    simp only [Set.mem_image2, Set.mem_range, exists_exists_eq_and]
    use ⟨s.stack, s.heap ∪ heap⟩, ⟨s.stack, heap⟩
    rfl

/-! Theorems related to range and their approximation -/
section Range

theorem nonempty_range {f : StateRV Var} : Set.Nonempty (Set.range f) := by
  have s : State Var := ⟨fun _ => 0, fun _ => HeapValue.undef⟩
  use (f s)
  exact Set.mem_range_self s

theorem range_of_fslTrue : Set.range `[fsl Var| fTrue] = {1} := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    simp only [Set.mem_singleton_iff]
    rfl
  · intro h
    simp only [Set.mem_singleton_iff] at h
    rw [h]
    simp only [Set.mem_range]
    use inhabited_state.default
    rfl

theorem range_of_fslFalse : Set.range `[fsl Var| fFalse] = {0} := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · intro h
    obtain ⟨s, rfl⟩ := h
    simp only [Set.mem_singleton_iff]
    rfl
  · intro h
    simp only [Set.mem_singleton_iff] at h
    rw [h]
    simp only [Set.mem_range]
    use inhabited_state.default
    rfl

theorem range_of_fslEmp : Set.range `[fsl Var| emp] = {0,1} := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    rw [fslEmp]
    simp only [Set.mem_insert_iff, iteOneZero_eq_zero_def, Set.mem_singleton_iff,
      iteOneZero_eq_one_def]
    exact ne_or_eq s.heap ∅
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    cases h with
    | inl h =>
      rw [h]
      use ⟨inhabited_stack.default, fun l => if l = 1 then HeapValue.val 0 else HeapValue.undef⟩
      simp only [fslEmp, iteOneZero_eq_zero_def]
      intro h
      have := congrFun h 1
      simp only [↓reduceIte, reduceCtorEq] at this
    | inr h =>
      rw [h]
      use inhabited_state.default
      simp only [fslEmp, iteOneZero_eq_one_def]
      apply funext
      intro _
      rfl

theorem range_of_fslPointsTo : Set.range `[fsl Var| e ↦ e'] ⊆ {0,1} := by
  rintro i ⟨s, rfl⟩
  rw [fslPointsTo]
  simp only [Set.mem_insert_iff, iteOneZero_eq_zero_def, Set.mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [Or.comm]
  exact Classical.em _

theorem range_of_fslEquals : Set.range `[fsl Var| e = e'] ⊆ {0,1} := by
  rintro i ⟨s, rfl⟩
  rw [fslEquals]
  simp only [Set.mem_insert_iff, iteOneZero_eq_zero_def, Set.mem_singleton_iff,
    iteOneZero_eq_one_def]
  exact ne_or_eq (e s.stack) (e' s.stack)

theorem range_of_fslReal : Set.range `[fsl Var | <e> ] = Set.range e := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    simp only [fslReal, Set.mem_range, exists_apply_eq_apply]
  · rintro h
    simp only [Set.mem_range, fslReal]
    simp only [Set.mem_range] at h
    obtain ⟨stack, rfl⟩ := h
    use ⟨stack, inhabited_heap.default⟩

theorem range_of_fslIverson : Set.range `[fsl Var | ⁅p⁆] ⊆ {0,1} := by
  rintro i ⟨s,rfl⟩
  rw [fslIverson]
  simp only [Set.mem_insert_iff, iteOneZero_eq_zero_def, Set.mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [Or.comm]
  exact Classical.em _

theorem range_of_fslSubst : Set.range `[fsl Var| [[f]](x ↦ e)] ⊆ Set.range f := by
  rintro i ⟨s,rfl⟩
  rw [fslSubst]
  simp only [substituteStack, Set.mem_range, exists_apply_eq_apply]

theorem range_of_fslNot : Set.range `[fsl| ~[[f]]] = σ '' Set.range f := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    use s
    rfl
  · simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, forall_exists_index]
    rintro s rfl
    use s
    rfl

theorem range_of_fslMin :
    Set.range `[fsl| [[f₁]] ⊓ [[f₂]]] ⊆ Set.image2 min (Set.range f₁) (Set.range f₂) := by
  rintro i ⟨s, rfl⟩
  simp only [Set.mem_image2, Set.mem_range, exists_exists_eq_and]
  use s, s
  rfl

theorem range_of_fslMax :
    Set.range `[fsl| [[f₁]] ⊔ [[f₂]]] ⊆ Set.image2 max (Set.range f₁) (Set.range f₂) := by
  rintro i ⟨s, rfl⟩
  simp only [Set.mem_image2, Set.mem_range, exists_exists_eq_and]
  use s, s
  rfl

theorem range_of_fslAdd :
    Set.range `[fsl| [[f₁]] + [[f₂]]] ⊆ Set.image2 truncatedAdd (Set.range f₁) (Set.range f₂) := by
  rintro i ⟨s, rfl⟩
  simp only [Set.mem_image2, Set.mem_range, exists_exists_eq_and]
  use s, s
  rfl

theorem range_of_fslMul :
    Set.range `[fsl| [[f₁]] ⬝ [[f₂]]] ⊆ Set.image2 Mul.mul (Set.range f₁) (Set.range f₂) := by
  rintro i ⟨s, rfl⟩
  simp only [Set.mem_image2, Set.mem_range, exists_exists_eq_and]
  use s, s
  rfl

theorem range_of_fslSup {f : α → StateRV Var} (h_nonempty : Nonempty α) :
    Set.range `[fsl| S x. [[f x]]] ⊆ closure ({ i | ∃ x, i ∈ Set.range (f x)}) := by
  rintro i ⟨s, rfl⟩
  rw [fslSup]
  apply sSup_in_closure_of_subset
  · obtain ⟨_, ⟨x, _⟩⟩ := (nonempty_StateRV_set f s h_nonempty)
    use (f x s)
    simp only [Set.range, Subtype.exists, exists_prop, Set.mem_setOf_eq]
    use (f x)
    apply And.intro
    · use x
    · rfl
  · simp only [Set.range, Subtype.exists, exists_prop, Set.mem_setOf_eq, Set.setOf_subset_setOf,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x,rfl⟩
    use x, s

theorem range_of_fslSup_empty {f : α → StateRV Var} (h_empty : IsEmpty α) :
    Set.range `[fsl| S x. [[f x]]] = {0} := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    simp only [Set.mem_singleton_iff]
    apply le_antisymm
    · apply sSup_le
      simp only [Set.range, IsEmpty.exists_iff, Set.setOf_false, isEmpty_subtype,
        Set.mem_empty_iff_false, not_false_eq_true, implies_true, false_implies]
    · exact nonneg'
  · simp only [Set.mem_singleton_iff, Set.mem_range]
    rintro rfl
    use inhabited_state.default
    apply le_antisymm
    · apply sSup_le
      simp only [Set.mem_range, IsEmpty.exists_iff, Set.setOf_false, isEmpty_subtype,
        Set.mem_empty_iff_false, not_false_eq_true, implies_true, false_implies]
    · exact nonneg'

theorem range_of_fslSup_of_finite {f : α → StateRV Var}
    (h_nonempty : Nonempty α) (h_finite : Set.Finite { i | ∃ x, i ∈ Set.range (f x)}):
    Set.range `[fsl| S x. [[f x]]] ⊆ { i | ∃ x, i ∈ Set.range (f x)} := by
  rintro _ ⟨s, rfl⟩
  rw [fslSup]
  have h_nonempty : Set.Nonempty { i | ∃ x, i = f x s} := by {
    let x := Classical.choice h_nonempty
    use (f x s), x
  }
  have h_finite : Set.Finite { i | ∃ x, i = f x s} := by {
    apply Set.Finite.subset h_finite
    rintro i ⟨x,rfl⟩
    use x, s
  }
  obtain ⟨x,h⟩ := Set.Nonempty.csSup_mem h_nonempty h_finite
  use x, s
  rw [← h]
  apply le_antisymm
  · apply sSup_le_sSup
    rintro _ ⟨x, rfl⟩
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_exists_eq_and,
      exists_apply_eq_apply]
  · apply sSup_le_sSup
    rintro _ ⟨⟨fx,⟨x',h_fx⟩⟩,rfl⟩
    simp only [Set.mem_setOf_eq]
    use x'
    rw [← h_fx]

theorem range_of_fslInf {f : α → StateRV Var} (h_nonempty : Nonempty α) :
    Set.range `[fsl| I x. [[f x]]] ⊆ closure ({ i | ∃ x, i ∈ Set.range (f x)}) := by
  rintro i ⟨s, rfl⟩
  rw [fslInf]
  apply sInf_in_closure_of_subset
  · obtain ⟨_, ⟨x, _⟩⟩ := (nonempty_StateRV_set f s h_nonempty)
    use (f x s)
    simp only [Set.range, Subtype.exists, exists_prop, Set.mem_setOf_eq]
    use (f x)
    apply And.intro
    · use x
    · rfl
  · simp only [Set.range, Subtype.exists, exists_prop, Set.mem_setOf_eq, Set.setOf_subset_setOf,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x,rfl⟩
    use x, s

theorem range_of_fslInf_empty {f : α → StateRV Var} (h_empty : IsEmpty α) :
    Set.range `[fsl| I x. [[f x]]] = {1} := by
  rw [Set.ext_iff]
  intro i
  apply Iff.intro
  · rintro ⟨s, rfl⟩
    simp only [Set.mem_singleton_iff]
    apply le_antisymm
    · exact le_one'
    · apply le_sInf
      simp only [Set.range, IsEmpty.exists_iff, Set.setOf_false, isEmpty_subtype,
        Set.mem_empty_iff_false, not_false_eq_true, implies_true, false_implies]
  · simp only [Set.mem_singleton_iff, Set.mem_range]
    rintro rfl
    use inhabited_state.default
    apply le_antisymm
    · exact le_one'
    · apply le_sInf
      simp only [Set.mem_range, IsEmpty.exists_iff, Set.setOf_false, isEmpty_subtype,
        Set.mem_empty_iff_false, not_false_eq_true, implies_true, false_implies]

theorem range_of_fslInf_of_finite {f : α → StateRV Var}
    (h_nonempty : Nonempty α) (h_finite : Set.Finite { i | ∃ x, i ∈ Set.range (f x)}):
    Set.range `[fsl| I x. [[f x]]] ⊆ { i | ∃ x, i ∈ Set.range (f x)} := by
  rintro _ ⟨s, rfl⟩
  rw [fslInf]
  have h_nonempty : Set.Nonempty { i | ∃ x, i = f x s} := by {
    let x := Classical.choice h_nonempty
    use (f x s), x
  }
  have h_finite : Set.Finite { i | ∃ x, i = f x s} := by {
    apply Set.Finite.subset h_finite
    rintro i ⟨x,rfl⟩
    use x, s
  }
  obtain ⟨x,h⟩ := Set.Nonempty.csInf_mem h_nonempty h_finite
  use x, s
  rw [← h]
  apply le_antisymm
  · apply sInf_le_sInf
    rintro _ ⟨⟨fx,⟨x',h_fx⟩⟩,rfl⟩
    simp only [Set.mem_setOf_eq]
    use x'
    rw [← h_fx]
  · apply sInf_le_sInf
    rintro _ ⟨x, rfl⟩
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_exists_eq_and,
      exists_apply_eq_apply]

theorem range_of_fslSepMul :
    Set.range `[fsl| [[f₁]] ⋆ [[f₂]]] ⊆ closure (Set.image2 Mul.mul (Set.range f₁) (Set.range f₂)) := by
  intro i ⟨s,h⟩
  rw [← h]
  apply sSup_in_closure_of_subset
  · use (f₁ ⟨s.stack, ∅⟩) * (f₂ s)
    use ∅, s.heap, emptyHeap_disjoint', emptyHeap_union'
  · rintro _ ⟨heap₁, heap₂, _, _, rfl⟩
    simp only [Set.image2, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
    use ⟨s.stack, heap₁⟩, ⟨s.stack, heap₂⟩
    rfl

theorem range_of_fslSepMul_of_finite_range
    (h_finite₁ : Set.Finite (Set.range f₁)) (h_finite₂ : Set.Finite (Set.range f₂)) :
    Set.range `[fsl| [[f₁]] ⋆ [[f₂]]] ⊆ Set.image2 Mul.mul (Set.range f₁) (Set.range f₂) := by
  simp only [Set.range, Set.image2, Set.mem_setOf_eq, exists_exists_eq_and, Set.setOf_subset_setOf,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro s
  obtain ⟨heap₁, heap₂, _, _, h⟩ := exists_fslSepMul_max_of_finite_values s h_finite₁ h_finite₂
  rw [h]
  use ⟨s.stack, heap₁⟩, ⟨s.stack, heap₂⟩
  rfl

theorem range_of_fslSepInf :
    Set.range `[fsl| [[f₁]] -⋆ [[f₂]]] ⊆ closure (Set.image2 Div.div (Set.range f₂) (Set.range f₁)) := by
  intro i ⟨s,h⟩
  rw [← h]
  apply sInf_in_closure_of_subset
  · use (f₂ s) / (f₁ ⟨s.stack, ∅⟩)
    use ∅
    rw [State.disjoint_comm]
    use emptyHeap_disjoint'
    rw [union_emptyHeap']
  · rintro _ ⟨heap, _, rfl⟩
    simp only [Set.image2, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
    use ⟨s.stack, s.heap ∪ heap⟩, ⟨s.stack, heap⟩
    rfl

theorem range_of_fslSepDiv_of_finite_range
    (h_finite₁ : Set.Finite (Set.range f₁)) (h_finite₂ : Set.Finite (Set.range f₂)) :
    Set.range `[fsl| [[f₁]] -⋆ [[f₂]]] ⊆ Set.image2 Div.div (Set.range f₂) (Set.range f₁) := by
  simp only [Set.range, Set.image2, Set.mem_setOf_eq, exists_exists_eq_and, Set.setOf_subset_setOf,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro s
  obtain ⟨heap, _, h⟩ := exists_fslSepDiv_min_of_finite_values s h_finite₁ h_finite₂
  rw [h]
  use ⟨s.stack, s.heap ∪ heap⟩, ⟨s.stack, heap⟩
  rfl

end Range

/-! Theorems to translate an fsl into sl -/
section Transform

/-- Transform a fsl entailment into a qualtitative entailment-/
theorem fsl_entail_if_atLeast (f g : StateRV Var) {values : Set I} (h_subset : Set.range f ⊆ values) :
    f ⊢ g ↔ ∀ i ∈ values, `[sl| [[λ s => i ≤ f s]] ⊢ [[fun s => i ≤ g s]]] := by
  apply Iff.intro
  · intro h i _ s h_f
    calc i
      _ ≤ f s := h_f
      _ ≤ g s := h s
  · intro h s
    refine h (f s) ?_ s (le_refl (f s))
    exact Set.mem_of_subset_of_mem h_subset (Set.mem_range_self _)

/-! Theorems transformting the atLeast expressions from the previous theorem into
  separation logic objects. -/

theorem zero_le_atLeast (f : StateRV Var) (s : State Var) : 0 ≤ f s ↔ `[sl Var| sTrue] s := by
  apply Iff.intro
  · intro _; exact rfl
  · intro _; exact nonneg'

theorem atLeast_fslTrue_iff {i : I} (s : State Var) : i ≤ `[fsl Var| fTrue] s ↔ `[sl Var| sTrue] s := by
  apply Iff.intro
  · intro _; exact rfl
  · intro _; exact le_one'

theorem atLeast_fslFalse_iff {i : I} (s : State Var) (h_pos : 0 < i) :
    i ≤ `[fsl Var| fFalse] s ↔ `[sl Var| sFalse] s := by
  apply Iff.intro
  · intro h
    exfalso
    rw [← not_lt] at h
    exact h h_pos
  · intro h
    exfalso
    rw [slFalse, Bool.false_eq_true] at h
    exact h

theorem atLeast_fslEmp_iff {i : I} (h_lt : 0 < i) (s : State Var) :
    i ≤ `[fsl| emp] s ↔ `[sl| emp] s := by
  apply Iff.intro
  · intro h
    unfold slEmp
    split
    unfold fslEmp at h
    simp only at h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    unfold fslEmp
    split
    unfold slEmp at h
    simp only at h
    rw [iteOneZero_eq_one_def.mpr h]
    exact le_one'

theorem atLeast_fslPointsTo_iff {i : I} (h_lt : 0 < i) (s : State Var) :
    i ≤ `[fsl| l ↦ l'] s ↔ `[sl| l ↦ l'] s := by
  unfold slPointsTo fslPointsTo
  apply Iff.intro
  · intro h
    split
    simp only at h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    simp only at h
    simp only
    rw [iteOneZero_eq_one_def.mpr h]
    exact le_one'

theorem atLeast_fslReal_iff {i : I} {e : ProbExp Var} (s : State Var) :
    i ≤ `[fsl| <e>] s ↔ i ≤ (e s.stack) := ⟨fun h => h, fun h => h⟩

theorem atLeast_fslIverson_iff {i : I} (h_lt : 0 < i) (P : State Var → Prop) (s : State Var) :
    i ≤ `[fsl| ⁅P⁆] s ↔ P s := by
  unfold fslIverson
  apply Iff.intro
  · intro h
    have : iteOneZero (_) = 1 := iteOneZero_of_non_one <| ne_of_lt <| lt_of_lt_of_le h_lt h
    rw [iteOneZero_eq_one_def] at this
    exact this
  · intro h
    rw [iteOneZero_pos h]
    exact le_one'

theorem atLeast_fslSubst_iff {i : I} {f : StateRV Var} {v : Var} {e : ValueExp Var} (s : State Var) :
    i ≤ `[fsl| [[f]](v ↦ e)] s ↔ `[sl| [[fun s => i ≤ f s]](v ↦ e)] s := ⟨fun h => h, fun h => h⟩

theorem atLeast_fslNot_of_slNot {i : I } {f : StateRV Var} {s : State Var} {values : Set I}
  (h_subset : Set.range f ⊆ values) :
    `[sl| ¬ [[fun s => sInf {j ∈ values | σ i < j } ≤ f s]]] s → i ≤ `[fsl| ~[[f]]] s := by
  unfold slNot fslNot
  intro h
  rw [le_symm_iff_le_symm, ← not_lt]
  intro h_lt
  apply h
  apply sInf_le
  apply And.intro
  · exact Set.mem_of_subset_of_mem h_subset (Set.mem_range_self _)
  · exact h_lt

theorem atLeast_fslNot_iff {i : I} {f : StateRV Var} {s : State Var} {values : Set I}
  (h_subset : Set.range f ⊆ values) (h_min : σ i < sInf {j ∈ values | σ i < j }) :
    i ≤ `[fsl| ~[[f]]] s ↔ `[sl| ¬ [[fun s => sInf {j ∈ values | σ i < j } ≤ f s]]] s := by
  apply Iff.intro
  · unfold slNot fslNot
    intro h
    rw [not_le]
    rw [le_symm_iff_le_symm] at h
    apply lt_of_le_of_lt h; clear h
    exact h_min
  · exact atLeast_fslNot_of_slNot h_subset

theorem atLeast_fslMin_iff {i : I} {f₁ f₂ : StateRV Var} {s : State Var} :
    i ≤ `[fsl| [[f₁]] ⊓ [[f₂]]] s ↔ `[sl| [[fun s => i ≤ f₁ s]] ∧ [[fun s => i ≤ f₂ s]]] s := by
  rw [ fslMin, slAnd, Pi.inf_apply, Pi.inf_apply ]
  apply Iff.intro
  · intro h
    rw [inf_eq_min, min_def] at h
    split at h
    case isTrue h_le =>
      apply And.intro
      · exact h
      · exact le_trans h h_le
    case isFalse h_lt =>
      rw [not_le] at h_lt
      apply And.intro
      · exact le_of_lt <| lt_of_le_of_lt h h_lt
      · exact h
  · rintro ⟨h₁, h₂⟩
    rw [inf_eq_min, min_def]
    split
    case isTrue h_le => exact h₁
    case isFalse h_lt => exact h₂

theorem atLeast_fslMax_iff {i : I} {f₁ f₂ : StateRV Var} {s : State Var} :
    i ≤ `[fsl| [[f₁]] ⊔ [[f₂]]] s ↔ `[sl| [[fun s => i ≤ f₁ s]] ∨ [[fun s => i ≤ f₂ s]]] s := by
  rw [ fslMax, slOr, Pi.sup_apply, Pi.sup_apply ]
  apply Iff.intro
  · intro h
    rw [sup_eq_max, max_def] at h
    split at h
    case isTrue h_le =>
      apply Or.inr
      exact h
    case isFalse h_lt =>
      apply Or.inl
      rw [not_le] at h_lt
      exact h
  · rintro (h | h)
    · rw [sup_eq_max, max_def]
      split
      case isTrue h_le => refine le_trans h h_le
      case isFalse h_lt => exact h
    · rw [sup_eq_max, max_def]
      split
      case isTrue h_le => exact h
      case isFalse h_lt => rw [not_le] at h_lt; refine le_trans h (le_of_lt h_lt)

theorem atLeast_fslAdd_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : Set.range f₁ ⊆ values₁) (h_subset₂ : Set.range f₂ ⊆ values₂) :
    i ≤ `[fsl| [[f₁]] + [[f₂]]] s
    ↔ ∃ i₁ ∈ values₁, ∃ i₂ ∈ values₂, i ≤ (i₁:ℝ) + i₂ ∧ `[sl| [[fun s => i₁ ≤ f₁ s]] ∧ [[fun s => i₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    use (f₁ s), (Set.mem_of_subset_of_mem h_subset₁ (Set.mem_range_self _))
    use (f₂ s), (Set.mem_of_subset_of_mem h_subset₂ (Set.mem_range_self _))
    rw [ fslAdd, le_truncatedAdd] at h
    use h, le_rfl
  · rintro ⟨i₁, _, i₂, _, h_i, h₁, h₂⟩
    rw [ fslAdd, le_truncatedAdd]
    rw [ Subtype.mk_le_mk] at h₁ h₂
    calc (i:ℝ)
    _ ≤ (i₁:ℝ) + i₂ := h_i
    _ ≤ (f₁ s) + i₂ := add_le_add_right h₁ ↑i₂
    _ ≤ (f₁ s) + (f₂ s) := add_le_add_left h₂ (f₁ s)

theorem atLeast_fslMul_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : Set.range f₁ ⊆ values₁) (h_subset₂ : Set.range f₂ ⊆ values₂) :
    i ≤ `[fsl| [[f₁]] ⬝ [[f₂]]] s
    ↔ ∃ i₁ ∈ values₁, ∃ i₂ ∈ values₂, i ≤ i₁ * i₂ ∧ `[sl| [[fun s => i₁ ≤ f₁ s]] ∧ [[fun s => i₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    use (f₁ s), (Set.mem_of_subset_of_mem h_subset₁ (Set.mem_range_self _))
    use (f₂ s), (Set.mem_of_subset_of_mem h_subset₂ (Set.mem_range_self _))
    rw [ fslMul] at h
    use h, le_rfl
  · rintro ⟨i₁, _, i₂, _, h_i, h₁, h₂⟩
    rw [ fslMul ]
    calc i
    _ ≤ i₁ * i₂ := h_i
    _ ≤ (f₁ s) * i₂ := mul_le_mul_of_nonneg_right h₁ nonneg'
    _ ≤ (f₁ s) * (f₂ s) := mul_le_mul_of_nonneg_left h₂ nonneg'

theorem atLeast_fslSup_if {α : Type} { i : I } {f : α → StateRV Var} {s : State Var} :
    `[sl| ∃ x. [[fun s => i ≤ f x s]]] s → i ≤ `[fsl| S x. [[f x]]] s := by
  rw [fslSup_apply, slExists_apply ]
  rintro ⟨x, h⟩
  rw [le_iSup_iff]
  intro j hj
  calc i
  _ ≤ f x s := h
  _ ≤ j := hj x

theorem atLeast_fslSup_iff {α : Type} { i : I } {f : α → StateRV Var} {s : State Var}
    (h_max : sSup { i | ∃ y, f y s = i } ∈ { i | ∃ y, f y s = i }) :
    i ≤ `[fsl| S x. [[f x]]] s ↔ `[sl| ∃ x. [[fun s => i ≤ f x s]]] s := by
  apply Iff.intro
  · rw [fslSup_apply, slExists_apply ]
    intro h
    obtain ⟨x, h_max⟩ := h_max
    use x
    rw [h_max]
    exact h
  · exact atLeast_fslSup_if


theorem atLeast_fslInf_iff {α : Type} { i : I } {f : α → StateRV Var} {s : State Var} :
    i ≤ `[fsl| I x. [[f x]]] s ↔ `[sl| ∀ x. [[fun s => i ≤ f x s]]] s := by
  rw [fslInf_apply, slAll_apply]
  apply Iff.intro
  · intro h x
    rw [le_iInf_iff] at h
    apply h x
  · rintro h
    rw [le_iInf_iff]
    rintro x
    exact h x

theorem atLeast_fslSepMul_if { i : I } {f₁ f₂ : StateRV Var} {s : State Var} :
    (∃ j₁, ∃ j₂, i ≤ j₁ * j₂ ∧ `[sl| [[fun s => j₁ ≤ f₁ s]] ∗ [[fun s => j₂ ≤ f₂ s]]] s)
    → i ≤ `[fsl| [[f₁]] ⋆ [[f₂]]] s := by
  rintro ⟨j₁, j₂, hi_le, ⟨heap₁, heap₂, h₁, h₂, h_disjoint, h_union⟩⟩
  rw [fslSepMul, le_sSup_iff]
  rintro j h
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
  calc i
  _ ≤ j₁ * j₂ := hi_le
  _ ≤ (f₁ ⟨s.stack, heap₁⟩) * j₂ := mul_le_mul_of_nonneg_right h₁ nonneg'
  _ ≤ (f₁ ⟨s.stack, heap₁⟩) * (f₂ ⟨s.stack, heap₂⟩) := mul_le_mul_of_nonneg_left h₂ nonneg'
  _ ≤ j := (h heap₁ heap₂ h_disjoint h_union rfl)

theorem atLeast_fslSepMul_iff { i : I } {f₁ f₂ : StateRV Var} {s : State Var} {values₁ values₂ : Set I}
    (h_subset₁ : Set.range f₁ ⊆ values₁) (h_subset₂ : Set.range f₂ ⊆ values₂)
    (h_max : `[fsl| [[f₁]] ⋆ [[f₂]]] s ∈
      { i | ∃ heap₁ heap₂, disjoint heap₁ heap₂ ∧ heap₁ ∪ heap₂ = s.heap
      ∧ i = f₁ ⟨s.stack, heap₁⟩ * f₂ ⟨s.stack, heap₂⟩ }) :
    i ≤ `[fsl| [[f₁]] ⋆ [[f₂]]] s
    ↔ ∃ j₁ ∈ values₁, ∃ j₂ ∈ values₂, i ≤ j₁ * j₂
      ∧ `[sl| [[fun s => j₁ ≤ f₁ s]] ∗ [[fun s => j₂ ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h
    obtain ⟨heap₁, heap₂, h_disjoint, h_union, h_max⟩ := h_max
    rw [h_max] at h; clear h_max
    use (f₁ ⟨s.stack, heap₁⟩), (Set.mem_of_subset_of_mem h_subset₁ (Set.mem_range_self _))
    use (f₂ ⟨s.stack, heap₂⟩), (Set.mem_of_subset_of_mem h_subset₂ (Set.mem_range_self _))
    use h, heap₁, heap₂
  · rintro ⟨j₁, _, j₂, _, h⟩
    apply atLeast_fslSepMul_if
    use j₁, j₂

theorem atLeast_fslSepDiv_if_of_left_one_zero {i : I} {f₁ f₂ : StateRV Var} {s : State Var}
    (h_one_zero : Set.range f₁ = {0, 1}) :
    (`[sl| [[fun s => 1 ≤ f₁ s]] -∗ [[fun s => i ≤ f₂ s]]] s)
    → i ≤ `[fsl| [[f₁]] -⋆ [[f₂]]] s := by
  intro h
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  specialize h heap h_disjoint
  rw [Set.ext_iff] at h_one_zero
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at h_one_zero
  specialize h_one_zero (f₁ ⟨s.stack,heap⟩)
  cases h_one_zero.mp ⟨⟨s.stack,heap⟩, rfl⟩ with
  | inl h_zero =>
    rw [h_zero, unit_div_zero]
    exact le_one'
  | inr h_one =>
    rw [h_one, unit_div_one]
    simp only at h
    rw [h_one] at h
    exact h le_rfl

theorem atLeast_fslSepDiv_iff_of_left_one_zero {f₁ f₂ : StateRV Var} {s : State Var}
    (h_one_zero : Set.range f₁ = {0, 1}) :
    i ≤ `[fsl| [[f₁]] -⋆ [[f₂]]] s
    ↔ `[sl| [[fun s => 1 ≤ f₁ s]] -∗ [[fun s => i ≤ f₂ s]]] s := by
  apply Iff.intro
  · intro h heap h_disjoint h_f₁
    rw [Set.ext_iff] at h_one_zero
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at h_one_zero
    specialize h_one_zero (f₁ ⟨s.stack,heap⟩)
    cases h_one_zero.mp ⟨⟨s.stack,heap⟩, rfl⟩ with
    | inl h_zero =>
      exfalso
      rw [h_zero, ← not_lt] at h_f₁
      exact h_f₁ zero_lt_one
    | inr h_one =>
      rw [fslSepDiv, le_sInf_iff] at h
      specialize h (f₂ ⟨s.stack, s.heap ∪ heap⟩)
      apply h
      use heap, h_disjoint
      rw [h_one, unit_div_one]
  · exact atLeast_fslSepDiv_if_of_left_one_zero h_one_zero

end Transform

end Qsl2Sl
