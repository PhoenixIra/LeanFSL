import Mathlib.Topology.UnitInterval

/-
This file contains lemmas and definitions used
in conjunction with unitInterval reasoning interpreted as probabilities
-/


namespace unitInterval

open Classical Set.Icc

noncomputable instance unit_cl : CompleteLattice I := Set.Icc.completeLattice (by simp)

lemma div_le_one {a b : ℝ} (h_b_pos : 0 < b) (h_ab : a ≤ b): a/b ≤ 1 := by
  have h_b_nonneg : 0 ≤ b := by apply le_iff_lt_or_eq.mpr; left; exact h_b_pos
  have : b ≤ b := by apply le_iff_lt_or_eq.mpr; right; rfl
  calc a / b ≤ b / b    := by exact (div_le_div h_b_nonneg h_ab h_b_pos this)
           _ = b * b⁻¹  := by rewrite[div_eq_mul_inv]; rfl
           _ = 1        := by refine mul_inv_cancel (ne_of_gt h_b_pos)

lemma div_mem_unit {a b : ℝ} (h_a_nonneg : 0 ≤ a) (h_ab : a ≤ b): a/b ∈ I := by
  have h_b_nonneg: 0 ≤ b := by apply le_trans; exact h_a_nonneg; exact h_ab
  simp; apply And.intro;
  . exact div_nonneg h_a_nonneg h_b_nonneg
  . rewrite [le_iff_lt_or_eq] at h_b_nonneg
    cases h_b_nonneg with
    | inl h_b_pos => exact div_le_one h_b_pos h_ab
    | inr h_b_zero => rewrite [←h_b_zero, div_zero]; simp

noncomputable def unitDiv (i j : I) : I := if h : i ≤ j then ⟨i/j, div_mem_unit nonneg' h⟩ else 1
noncomputable instance unitHasDiv : Div I := ⟨unitDiv⟩

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

lemma iteOneZero_def {P :Prop} : iteOneZero P = i ↔ i = 0 ∧ ¬ P ∨ i = 1 ∧ P := by
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



end unitInterval
