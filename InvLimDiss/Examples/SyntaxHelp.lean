import InvLimDiss.Program

open Syntax

def var (var : String) : ValueExp String :=
  λ s => s var

def const (val : ℚ) : ValueExp String :=
  λ _ => val

def eq (l r : ValueExp String) : BoolExp String :=
  λ s => l s = r s

noncomputable def half : ProbExp String := fun _ =>
  ⟨1/2, unitInterval.div_mem zero_le_one zero_le_two one_le_two⟩

noncomputable def one : ProbExp String := fun _ => 1

theorem varValue_of_var : varValue (var v) = {v} := by
  unfold varValue
  apply Set.Subset.antisymm
  · rintro t ⟨s, q, h⟩
    simp only [Set.mem_singleton_iff]
    unfold var at h
    unfold State.substituteVar at h
    split_ifs at h
    case pos h_eq => exact h_eq
    case neg h_ne => exfalso; exact h rfl
  · simp only [ne_eq, Set.singleton_subset_iff, Set.mem_setOf_eq]
    use (fun _ => 0), 1
    simp only [var, State.substituteVar, ↓reduceIte, one_ne_zero, not_false_eq_true]

theorem varValue_of_const : varValue (const r) = ∅ := by
  unfold varValue
  apply Set.Subset.antisymm
  · rintro t ⟨s, q, h⟩
    exfalso
    unfold const at h
    exact h rfl
  · simp only [ne_eq, Set.empty_subset]

theorem varProb_of_one : varProb one = ∅ := by
  unfold varProb
  apply Set.Subset.antisymm
  · rintro r ⟨s, q, h⟩
    exfalso
    unfold one at h
    exact h rfl
  · simp only [ne_eq, Set.empty_subset]

theorem varProb_of_half : varProb half = ∅ := by
  unfold varProb
  apply Set.Subset.antisymm
  · rintro r ⟨s, q, h⟩
    exfalso
    unfold half at h
    exact h rfl
  · simp only [ne_eq, Set.empty_subset]
