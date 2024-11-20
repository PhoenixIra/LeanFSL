import InvLimDiss.Entailments.FSL2SL
import Mathlib.Tactic.Rify

namespace Counterexample

open Qsl2Sl unitInterval State FSL SL Syntax

theorem atLeast_fslSepDiv_iff {i : I} {f₁ f₂ : StateRV Var} {s : State Var}
    (h_min : `[fsl| [[f₁]] -⋆ [[f₂]]] s ∈ { x | ∃ heap, disjoint s.heap heap ∧
      x = f₂ ⟨s.stack,s.heap ∪ heap⟩ / f₁ ⟨s.stack,heap⟩})
    (h_finite : Set.Finite (Set.range f₁)) :
    i ≤ `[fsl| [[f₁]] -⋆ [[f₂]]] s
    ↔ ∃ j₁ ∈ Set.range f₁, ∃ j₂ ∈ Set.range f₂,  i ≤ j₂ / j₁
      ∧ `[sl| [[fun s => j₁ ≤ f₁ s]] -∗ [[fun s => j₂ ≤ f₂ s]]] s := sorry

example : False := by
  let s : State String := ⟨fun _ => 0, ∅⟩
  let f₁ : StateRV String := fun _ => 0
  let f₂ : StateRV String := fun ⟨_,h⟩ =>
    if let HeapValue.val x := h 1
      then if h : (0:ℝ) < x ∧ x ≤ (1:ℝ) then ⟨x,⟨le_of_lt h.left,h.right⟩⟩ else 1
      else 1
  have h_min : `[fsl| [[f₁]] -⋆ [[f₂]]] s ∈ { x | ∃ heap, disjoint s.heap heap ∧
      x = f₂ ⟨s.stack,s.heap ∪ heap⟩ / f₁ ⟨s.stack,heap⟩} := by {
    use ∅
    rw [State.disjoint_comm]
    use emptyHeap_disjoint'
    rw [fslSepDiv]
    apply le_antisymm
    · apply sInf_le
      use ∅
      rw [State.disjoint_comm]
      use emptyHeap_disjoint'
    · apply le_sInf
      rintro i ⟨heap₁, _, rfl⟩
      unfold_let f₁
      simp only [unit_div_zero, le_refl]
  }
  have h_finite : Set.Finite (Set.range f₁) := by {
    unfold_let f₁
    simp only [Set.range_const, Set.finite_singleton]
  }
  have : 1 ≤ `[fsl| [[f₁]] -⋆ [[f₂]]] s := by {
    simp only [fslSepDiv, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ _ _ rfl
    unfold_let f₁
    simp only [unit_div_zero, le_refl]
  }
  have := (atLeast_fslSepDiv_iff h_min h_finite).mp this
  obtain ⟨j₁, h_j₁, j₂, h_j₂, _, h⟩ := this
  rw [slSepImp] at h
  obtain ⟨s_j₂, h_j₂⟩ := h_j₂
  unfold_let f₂ at h_j₂
  simp only [Rat.cast_nonneg] at h_j₂
  split at h_j₂
  case h_1 _ =>
    split at h_j₂
    case isTrue x _ h_x' =>
      let heap_small : Heap := fun l => if l = 1 then HeapValue.val (x/2) else HeapValue.undef
      specialize h heap_small
      obtain ⟨s_j₁, h_j₁⟩ := h_j₁
      unfold_let f₁ at h_j₁
      simp only at h_j₁
      rw [← h_j₁] at h
      specialize h emptyHeap_disjoint' nonneg'
      rw [← h_j₂] at h
      unfold_let f₂ heap_small at h
      simp only [emptyHeap_union, ↓reduceIte, Rat.cast_div, Rat.cast_ofNat, Nat.ofNat_pos] at h
      have : (0:ℝ) < ↑x / 2 ∧ ↑x / 2 ≤ (1:ℝ) := by {
          norm_cast
          apply And.intro
          · rify
            linarith
          · rify
            linarith
      }
      rw [dif_pos this] at h
      rw [Subtype.mk_le_mk, ← not_lt] at h
      norm_cast at h
      have : x / 2 < x := by rify; exact div_two_lt_of_pos h_x'.left
      exact h this
    case isFalse h_x =>
      let heap_small : Heap := fun l => if l = 1 then HeapValue.val (1/2) else HeapValue.undef
      specialize h heap_small
      obtain ⟨s_j₁, h_j₁⟩ := h_j₁
      unfold_let f₁ at h_j₁
      simp only at h_j₁
      rw [← h_j₁] at h
      specialize h emptyHeap_disjoint' nonneg'
      rw [← h_j₂] at h
      unfold_let f₂ heap_small at h
      simp only [one_div, emptyHeap_union, ↓reduceIte, Rat.cast_inv, Rat.cast_ofNat, inv_pos,
        Nat.ofNat_pos, true_and] at h
      have : (2:ℝ)⁻¹ ≤ 1 := by rw [inv_le_comm₀ zero_lt_two zero_lt_one, inv_one]; exact one_le_two
      rw [dif_pos this] at h
      rw [Subtype.mk_le_mk, Set.Icc.coe_one, le_inv_comm₀ zero_lt_one zero_lt_two, inv_one, ← not_lt] at h
      exact h one_lt_two
  case h_2 h_ne =>
    let heap_small : Heap := fun l => if l = 1 then HeapValue.val (1/2) else HeapValue.undef
    specialize h heap_small
    obtain ⟨s_j₁, h_j₁⟩ := h_j₁
    unfold_let f₁ at h_j₁
    simp only at h_j₁
    rw [← h_j₁] at h
    specialize h emptyHeap_disjoint' nonneg'
    rw [← h_j₂] at h
    unfold_let f₂ heap_small at h
    simp only [one_div, emptyHeap_union, ↓reduceIte, Rat.cast_inv, Rat.cast_ofNat, inv_pos,
      Nat.ofNat_pos, true_and] at h
    have : (2:ℝ)⁻¹ ≤ 1 := by rw [inv_le_comm₀ zero_lt_two zero_lt_one, inv_one]; exact one_le_two
    rw [dif_pos this] at h
    rw [Subtype.mk_le_mk, Set.Icc.coe_one, le_inv_comm₀ zero_lt_one zero_lt_two, inv_one, ← not_lt] at h
    exact h one_lt_two





end Counterexample
