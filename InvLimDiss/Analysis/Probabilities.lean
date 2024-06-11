import Mathlib.Topology.UnitInterval

/-
This file contains lemmas and definitions used
in conjunction with unitInterval reasoning interpreted as probabilities
-/


namespace unitInterval

open Classical Set.Icc

noncomputable instance unit_cl : CompleteLinearOrder I := Set.Icc.completeLinearOrder (by simp)

instance : PosMulMono I where
  elim := by
    intro s i₁ i₂ h_i
    simp only [← Subtype.coe_le_coe, coe_mul]
    apply mul_le_mul
    · exact Eq.ge rfl
    · exact h_i
    · exact nonneg'
    · exact nonneg'

instance : MulPosMono I where
  elim := by
    intro s i₁ i₂ h_i; simp only
    simp only [← Subtype.coe_le_coe, coe_mul]
    apply mul_le_mul
    · exact h_i
    · exact Eq.ge rfl
    · exact nonneg'
    · exact nonneg'


lemma div_le_one {a b : ℝ} (h_b_pos : 0 < b) (h_ab : a ≤ b): a/b ≤ 1 := by
  have h_b_nonneg : 0 ≤ b := by apply le_iff_lt_or_eq.mpr; left; exact h_b_pos
  have : b ≤ b := by apply le_iff_lt_or_eq.mpr; right; rfl
  calc a / b ≤ b / b    := by exact (div_le_div h_b_nonneg h_ab h_b_pos this)
           _ = b * b⁻¹  := by rewrite[div_eq_mul_inv]; rfl
           _ = 1        := by refine mul_inv_cancel (ne_of_gt h_b_pos)

lemma div_mem_unit {a b : ℝ} (h_a_nonneg : 0 ≤ a) (h_ab : a < b): a/b ∈ I := by
  have h_b_pos: 0 < b := by apply lt_of_le_of_lt; exact h_a_nonneg; exact h_ab
  simp; apply And.intro;
  . exact div_nonneg h_a_nonneg (le_of_lt h_b_pos)
  . exact div_le_one h_b_pos (le_of_lt h_ab)

noncomputable instance unitDiv : Div I :=
    ⟨fun i j => if h : i < j then ⟨i/j, div_mem_unit nonneg' h⟩ else 1⟩

lemma unit_div_le_div {i j k l : I} (h_j : (0:ℝ) < l) (hik : i ≤ k) (hlj : l ≤ j) : i / j ≤ k / l := by
  unfold instHDiv unitDiv; simp only
  split
  case isTrue =>
    split
    case isTrue =>
      simp only [Subtype.mk_le_mk]
      apply div_le_div
      · exact nonneg'
      · exact hik
      · exact h_j
      · exact hlj
    case isFalse => exact le_one'
  case isFalse hij =>
    split
    case isTrue hkl => exfalso; exact hij <| lt_of_le_of_lt hik <| lt_of_lt_of_le hkl hlj
    case isFalse => exact Eq.le rfl

lemma unit_le_div_iff_mul_le (i j k : I) (h : 0 < k) : i ≤ j / k ↔ i * k ≤ j := by
  unfold instHDiv unitDiv
  simp only [← Subtype.coe_le_coe, coe_mul]
  apply Iff.intro
  · intro h_div
    split at h_div
    case isTrue =>
      have : (0:ℝ) < k := h
      apply (le_div_iff this).mp
      exact h_div
    case isFalse h_jk =>
      simp at h_jk
      exact le_trans mul_le_right h_jk
  · intro h_mul
    split
    case isTrue =>
      have : (0:ℝ) < k := h
      apply (le_div_iff this).mpr
      exact h_mul
    case isFalse => exact le_one'

lemma unit_div_zero (i : I) : i / 0 = 1 := by
  simp only [instHDiv, unitDiv, coe_zero, dite_eq_right_iff]
  intro h
  exfalso
  rw [← not_le] at h
  exact h nonneg'

lemma unit_div_of_lt {i j : I} (h : i < j) : ((i / j):I) = (i:ℝ) / j := by
  simp only [instHDiv, unitDiv, dif_pos h]

lemma unit_div_of_le {i j : I} (h : j ≤ i) : i / j = 1 := by
  simp only [instHDiv, unitDiv, dite_eq_right_iff]
  intro h'
  exfalso
  rw [← not_le] at h'
  exact h' h

lemma unit_div_eq_one_iff {i j : I} : i / j = 1 ↔ j ≤ i := by
  apply Iff.intro
  · intro h
    rw [HDiv.hDiv, instHDiv, unitDiv] at h
    simp only [dite_eq_right_iff] at h
    sorry

  · intro h
    exact unit_div_of_le h

lemma eq_zero_iff_sym_eq_one : σ x = 1 ↔ x = 0 := by
  apply Iff.intro
  · intro h
    rw [← unitInterval.symm_zero] at h
    exact symm_bijective.injective h
  · intro h
    rw [h]
    exact symm_zero

lemma eq_one_iff_sym_eq_zero : σ x = 0 ↔ x = 1 := by
  apply Iff.intro
  · intro h
    rw [← unitInterval.symm_one] at h
    exact symm_bijective.injective h
  · intro h
    rw [h]
    exact symm_one

noncomputable def ite_unit (P : Prop) (i j : I) : I := if P then i else j

lemma ite_unit_pos {P : Prop} (i j : I) (h : P) : ite_unit P i j = i := by
  unfold ite_unit
  exact if_pos h

lemma ite_unit_neg {P : Prop} (i j : I) (h : ¬ P) : ite_unit P i j = j := by
  unfold ite_unit
  exact if_neg h

lemma ite_unit_self {P : Prop} (i : I) :
    ite_unit P i i = i := by
  simp only [ite_unit, ite_self]

lemma ite_unit_def_of_ne {P : Prop} {i j : I} (h_ne : i ≠ j):
    (ite_unit P i j = i ↔ P) ∧ (ite_unit P i j = j ↔ ¬ P) := by
  apply And.intro
  · apply Iff.intro
    · intro h; rw [ite_unit, ite_eq_left_iff] at h
      exact of_not_not <| Not.imp (Ne.symm h_ne) h
    · intro h; exact ite_unit_pos i j h
  · apply Iff.intro
    · intro h; rw [ite_unit, ite_eq_right_iff] at h
      exact Not.imp h_ne h
    · intro h; exact ite_unit_neg i j h

noncomputable def iteOneZero (P : Prop) : I := ite_unit P 1 0

lemma iteOneZero_pos {P : Prop} (h : P) : iteOneZero P = 1 := by
  unfold iteOneZero
  exact ite_unit_pos 1 0 h

lemma iteOneZero_true : iteOneZero True = 1 := iteOneZero_pos True.intro

lemma iteOneZero_neg {P : Prop} (h : ¬P) : iteOneZero P = 0 := by
  unfold iteOneZero
  exact ite_unit_neg 1 0 h

lemma iteOneZero_false : iteOneZero False = 0 := iteOneZero_neg (fun h => h.elim)

lemma iteOneZero_eq_one_def {P : Prop} : iteOneZero P = 1 ↔ P := by
  unfold iteOneZero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).1

lemma iteOneZero_eq_zero_def {P : Prop} : iteOneZero P = 0 ↔ ¬ P := by
  unfold iteOneZero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).2

lemma iteOneZero_def {P : Prop} : iteOneZero P = i ↔ i = 0 ∧ ¬ P ∨ i = 1 ∧ P := by
  apply Iff.intro
  · intro h
    by_cases h_p : P
    · apply Or.inr
      rw [iteOneZero_pos h_p] at h
      apply And.intro h.symm
      exact h_p
    · apply Or.inl
      rw [iteOneZero_neg h_p] at h
      apply And.intro h.symm
      exact h_p
  · intro h
    cases h with
    | inl h => rw [iteOneZero_neg h.right]; exact h.left.symm
    | inr h => rw [iteOneZero_pos h.right]; exact h.left.symm

lemma iteOneZero_of_non_one {P : Prop}  (h : 0 ≠ iteOneZero P) : iteOneZero P = 1 := by
  unfold iteOneZero ite_unit at h
  split at h
  case isTrue h_P => exact iteOneZero_pos h_P
  case isFalse h_nP => exact (h rfl).elim

theorem truncatedAdd_mem_unit (i j : I) : min 1 ((i:ℝ) + j) ∈ I := by
  apply And.intro
  · exact le_min zero_le_one (add_nonneg i.property.1 j.property.1)
  · exact min_le_left 1 ((i:ℝ)+j)

noncomputable def truncatedAdd (i j : I) : I := ⟨min 1 (i + j), truncatedAdd_mem_unit i j⟩

theorem le_truncatedAdd (i j k : I) : i ≤ truncatedAdd j k ↔ i ≤ (j:ℝ) + k := by
  unfold truncatedAdd
  rw [Subtype.mk_le_mk]
  apply Iff.intro
  · intro h
    simp only [le_min_iff] at h
    exact h.right
  · intro h
    simp only [le_min_iff]
    exact ⟨le_one', h⟩

theorem le_symm_if_le_symm (i j : I) : i ≤ σ j → j ≤ σ i := by
  intro h
  rw [Subtype.mk_le_mk, coe_symm_eq] at h ⊢
  apply le_sub_left_of_add_le
  rw [add_comm]
  apply add_le_of_le_sub_left
  exact h

theorem le_symm_iff_le_symm (i j : I) : i ≤ σ j ↔ j ≤ σ i := ⟨le_symm_if_le_symm i j, le_symm_if_le_symm j i⟩

theorem symm_le_if_symm_le (i j : I) : σ i ≤ j → σ j ≤ i := by
  intro h
  rw [Subtype.mk_le_mk, coe_symm_eq] at h ⊢
  rw [sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add]
  exact h

theorem symm_le_iff_symm_le (i j : I) : σ i ≤ j ↔ σ j ≤ i := ⟨symm_le_if_symm_le i j, symm_le_if_symm_le j i⟩

theorem lt_symm_if_lt_symm (i j : I) : i < σ j → j < σ i := by
  intro h
  rw [Subtype.mk_lt_mk, coe_symm_eq] at h ⊢
  apply lt_sub_left_of_add_lt
  rw [add_comm]
  apply add_lt_of_lt_sub_left
  exact h

theorem lt_symm_iff_lt_symm (i j : I) : i < σ j ↔ j < σ i := ⟨lt_symm_if_lt_symm i j, lt_symm_if_lt_symm j i⟩

theorem symm_lt_if_symm_lt (i j : I) : σ i < j → σ j < i := by
  intro h
  rw [Subtype.mk_lt_mk, coe_symm_eq] at h ⊢
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact h

theorem symm_lt_iff_symm_lt (i j : I) : σ i < j ↔ σ j < i := ⟨symm_lt_if_symm_lt i j, symm_lt_if_symm_lt j i⟩

end unitInterval
