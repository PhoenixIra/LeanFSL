import LeanFSL.SL.Classical
import Mathlib.Tactic.Qify

/-!
  This file features various lemmas involing qualitative or classical separation logic.
  Especially we have:
  * Monotonicty theorems
  * Adjointness theorems
  * vanishing modus ponens
  * elimination rules for quantifiers
-/

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
  rw [slExists, iSup_apply, iSup, Set.range]
  simp only [eq_iff_iff, sSup_Prop_eq, Set.mem_setOf_eq]
  apply Iff.intro
  · rintro ⟨P, ⟨a, h_a⟩, h⟩
    rw [← h_a] at h
    use a
  · rintro ⟨x, hp⟩
    use (P x s); refine And.intro ?_ hp
    use x

theorem slAll_apply (P : α → StateProp Var) (s : State Var) :
    `[sl| ∀ x. [[P x]]] s ↔ ∀ x, P x s := by
  rw [slAll, iInf_apply, iInf, Set.range]
  simp only [eq_iff_iff, sInf_Prop_eq, Set.mem_setOf_eq, forall_exists_index]
  apply Iff.intro
  · rintro h x
    specialize h (P x s) x
    apply h
    rfl
  · intro h P' x h_P
    rw [← h_P]
    exact h x

theorem slBigSepCon_eq_one_iff_removedHeap {stack : Stack Var} {heap : Heap} :
    `[sl| [∗] i ∈ { ... n }. (∃ (x : ℚ). fun _ ↦ ↑↑l + ↑i ↦ x) ] ⟨stack, heap⟩
    ↔ heap = removedHeap heap l n ∧ isAlloc heap l n := by
  apply Iff.intro
  · intro h
    induction n generalizing heap with
    | zero =>
      simp only [removedHeap_of_zero]
      simp only [slBigSepCon, slEmp] at h
      apply And.intro h
      exact isAlloc_of_zero
    | succ n ih =>
      simp only [slBigSepCon] at h
      obtain ⟨heap₁, heap₂, h_left, h_right, _, h_union⟩ := h
      simp only [slExists_apply] at h_left
      obtain ⟨q, l', h_l', h_heap₁⟩ := h_left
      simp only [slPointsTo] at h_heap₁
      specialize ih h_right
      apply And.intro
      · rw [removedHeap_of_succ, ← h_union, h_heap₁, ih.left]
        apply funext
        intro l''
        split
        case isTrue h_l'' => rfl
        case isFalse h_l'' =>
          simp only [← Nat.cast_add, Nat.cast_inj] at h_l'
          have : l' = ⟨l + n, PNat.add_right_nat⟩ := by exact PNat.eq h_l'
          rw [this, singleton_union_of_neq, removedHeap_of_singleton_union,
            removedHeap_of_removedHeap]
          · apply Or.inr
            rw [← PNat.coe_le_coe]
            simp only [PNat.mk_coe]
            rfl
          · exact Ne.symm h_l''
      · intro l'' h_le h_lt
        simp_rw [← h_union]
        cases eq_or_ne l'' ⟨l + n, PNat.add_right_nat⟩ with
        | inl h_eq =>
          have : l'' = l' := by {
            rw [← PNat.coe_inj, PNat.mk_coe] at h_eq
            qify at h_eq
            simp only [← h_eq, Nat.cast_inj, PNat.coe_inj] at h_l'
            exact h_l'.symm
          }
          simp [this, Union.union, h_heap₁, State.singleton]
        | inr h_ne =>
          rw [union_eq_of_left_undef]
          · apply ih.right l'' h_le
            apply lt_of_le_of_ne
            · exact Nat.le_of_lt_succ h_lt
            · rw [ne_eq, ← PNat.coe_inj, PNat.mk_coe] at h_ne
              exact h_ne
          · simp_rw [h_heap₁]
            simp only [State.singleton, ite_eq_right_iff, reduceCtorEq, imp_false]
            intro h_eq
            apply h_ne
            rw [← PNat.coe_inj, PNat.mk_coe]
            qify
            simp only [← h_eq, h_l']
  · intro h
    rw [h.left]
    have h_alloc := h.right
    clear h
    induction n generalizing heap with
    | zero => simp only [slBigSepCon, slEmp, removedHeap_of_zero]
    | succ n ih =>
      simp only [slBigSepCon]
      by_cases ∃ (q : ℚ), heap ⟨l+n,PNat.add_right_nat⟩ = q
      case pos h_q =>
        obtain ⟨q, h_q⟩ := h_q
        use (singleton ⟨l+n, PNat.add_right_nat⟩ q), (removedHeap heap l n)
        apply And.intro
        · rw [slExists_apply]
          use q
          simp only [slPointsTo]
          use ⟨l+n,PNat.add_right_nat⟩
          apply And.intro (by simp only [PNat.mk_coe, Nat.cast_add])
          rfl
        · apply And.intro <| ih <| isAlloc_of_isAlloc_succ h_alloc
          apply And.intro disjoint_singleton_removedHeap
          rw [removedHeap_of_succ]
          apply funext
          intro l'
          split
          case isTrue h_l' =>
            rw [h_l']
            simp only [singleton_union, h_q]
          case isFalse h_l' =>
            rw [singleton_union_of_neq]
            exact Ne.symm h_l'
      case neg h =>
        exfalso
        rw [not_exists, ← undef_iff_forall_neq_val] at h
        apply h_alloc ⟨l+n,PNat.add_right_nat⟩
        · rw [← PNat.coe_le_coe, PNat.mk_coe]
          simp only [le_add_iff_nonneg_right, zero_le]
        · simp only [PNat.mk_coe, add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one]
        · exact h











end SL
