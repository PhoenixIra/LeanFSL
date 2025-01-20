import InvLimDiss.Program.State.Basic
import Mathlib.Data.Set.Finite.Powerset

namespace Finite

open State HeapValue Classical

/-- Lifting of finite to heap locations. -/
def Heap.Finite (heap : Heap) : Prop := Set.Finite { l | heap l ≠ undef}

private lemma powerset_finite (heap : Heap) (h_finite : Heap.Finite heap) :
    Set.Finite ({ns : Set PNat | ∀ n ∈ ns, heap n ≠ undef }) := by
  exact Set.Finite.finite_subsets h_finite


/-- Helper function for the rest of the proofs -/
private noncomputable def surjectiv_func (heap : Heap) (ns : Set PNat ) : Heap :=
  fun n => if n ∈ ns then heap n else undef

private lemma powerset_surjection (heap : Heap) (h_finite : Heap.Finite heap) :
    Set.Finite (surjectiv_func heap '' { ns : Set PNat | ∀ n ∈ ns, heap n ≠ undef}) := by
  apply Set.Finite.of_surjOn (surjectiv_func heap)
  · intro g h
    exact h
  · exact powerset_finite heap h_finite

/-- Proof that given a finite heap, the set of subheaps is also finite. -/
theorem finite_of_subheaps {heap : Heap} (h_finite : Heap.Finite heap) :
    Set.Finite {heap₁ | ∃ heap₂, heap₁ ∪ heap₂ = heap} := by
  have := powerset_surjection heap h_finite
  simp only [Set.image, ne_eq, Set.mem_setOf_eq] at this
  apply Set.Finite.subset this
  rintro heap₁ ⟨heap₂, h_heap⟩
  use {n | (∃ a, heap₁ n = val a)}
  apply And.intro
  · intro n ⟨_, h_heap₁⟩
    obtain h_heap := congrFun h_heap n
    simp only [Union.union, h_heap₁] at h_heap
    rw [← h_heap]
    simp only [reduceCtorEq, not_false_eq_true]
  · apply funext
    intro n
    obtain h_heap := congrFun h_heap n
    simp only [Union.union] at h_heap
    simp only [surjectiv_func, Set.mem_setOf_eq]
    split
    case isTrue h_heap₁ =>
      obtain ⟨_, h_heap₁⟩ := h_heap₁
      simp only [h_heap₁] at h_heap
      exact Eq.symm <| Eq.trans h_heap₁ h_heap
    case isFalse h_heap₁ =>
      simp only [not_exists] at h_heap₁
      split at h_heap
      case h_1 q h₁ =>
        exfalso
        exact h_heap₁ q h₁
      case h_2 h₁ =>
        exact h₁.symm

end Finite
