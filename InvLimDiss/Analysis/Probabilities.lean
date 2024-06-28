import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Rify
import Mathlib.Topology.Algebra.InfiniteSum.Basic

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

lemma nonneg_of_lt {i j : I} (h : i < j) : 0 < j :=
  lt_of_le_of_lt nonneg' h

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

lemma unitDiv_def {i j : I} :
    i / j = if h : i < j then ⟨i/j, div_mem_unit nonneg' h⟩ else 1 := rfl

lemma coe_div {i j : I} :
    ↑(i / j) = if i < j then (i/j : ℝ) else 1 := by
  rw [unitDiv_def]
  split <;> rfl

lemma unit_div_le_div {i j k l : I} (hik : i ≤ k) (hlj : l ≤ j) : i / j ≤ k / l := by
  rw [Subtype.mk_le_mk, coe_div, coe_div]
  split
  case isTrue =>
    split
    case isTrue h_kl =>
      cases eq_or_ne l 0 with
      | inl h_eq =>
        exfalso
        rw [h_eq, ← not_le] at h_kl
        exact h_kl nonneg'
      | inr h_ne =>
        apply div_le_div
        · exact nonneg'
        · exact hik
        · apply lt_of_le_of_ne nonneg'
          apply Ne.symm
          simp only [ne_eq, h_ne, not_false_eq_true]
        · exact hlj
    case isFalse h _ => exact (div_mem_unit nonneg' h).2
  case isFalse hij =>
    split
    case isTrue hkl => exfalso; exact hij <| lt_of_le_of_lt hik <| lt_of_lt_of_le hkl hlj
    case isFalse => exact Eq.le rfl

lemma unit_le_div_iff_mul_le {i j k : I} : i ≤ j / k ↔ i * k ≤ j := by
  rw [Subtype.mk_le_mk, coe_div]
  apply Iff.intro
  · intro h_div
    split at h_div
    case isTrue h_jk =>
      cases eq_or_ne k 0 with
      | inl h_eq =>
        exfalso
        rw [h_eq, ← not_le] at h_jk
        exact h_jk nonneg'
      | inr h_ne =>
        have : (0:ℝ) < k := by
          {apply lt_of_le_of_ne nonneg'; apply Ne.symm; simp only [ne_eq, h_ne, not_false_eq_true]}
        apply (le_div_iff this).mp
        exact h_div
    case isFalse h_jk =>
      simp at h_jk
      exact le_trans mul_le_right h_jk
  · intro h_mul
    split
    case isTrue h_jk =>
      cases eq_or_ne k 0 with
      | inl h_eq =>
        exfalso
        rw [h_eq, ← not_le] at h_jk
        exact h_jk nonneg'
      | inr h_ne =>
        have : (0:ℝ) < k := by
          {apply lt_of_le_of_ne nonneg'; apply Ne.symm; simp only [ne_eq, h_ne, not_false_eq_true]}
        apply (le_div_iff this).mpr
        exact h_mul
    case isFalse => exact le_one'

lemma unit_div_zero (i : I) : i / 0 = 1 := by
  rw [Subtype.mk_eq_mk, coe_div]
  simp only [coe_zero, div_zero, coe_one, ite_eq_right_iff, zero_ne_one, imp_false, not_lt]
  exact nonneg'

lemma zero_unit_div (i : I) (h : 0 < i) : 0 / i = 0 := by
  rw [Subtype.mk_eq_mk, coe_div]
  split_ifs
  simp only [coe_zero, zero_div]

lemma unit_div_one (i : I) : i / 1 = i := by
  rw [Subtype.mk_eq_mk, coe_div]
  split
  case isTrue h_lt =>
    rw [coe_one, div_one]
  case isFalse h_le =>
    rw [not_lt] at h_le
    exact le_antisymm h_le le_one'

lemma unit_div_of_lt {i j : I} (h : i < j) : ((i / j):I) = (i:ℝ) / j := by
  rw [coe_div, if_pos h]

lemma unit_div_of_le {i j : I} (h : j ≤ i) : i / j = 1 := by
  rw [Subtype.mk_eq_mk, coe_div]
  simp only [coe_one, ite_eq_right_iff]
  intro h'
  exfalso
  rw [← not_le] at h'
  exact h' h

lemma unit_div_eq_one_iff {i j : I} : i / j = 1 ↔ j ≤ i := by
  rw [Subtype.mk_eq_mk, coe_div]
  apply Iff.intro
  · intro h
    simp only [coe_one, ite_eq_right_iff] at h
    cases eq_or_ne j 0 with
    | inl h_zero => rw [h_zero]; exact nonneg'
    | inr h_n_zero =>
      cases lt_or_le i j with
      | inl h_lt =>
        exfalso
        obtain h := le_of_eq (h h_lt).symm
        have : 0 < j := by {apply lt_of_le_of_ne nonneg' (Ne.symm h_n_zero)}
        rw [le_div_iff this, one_mul, Subtype.coe_le_coe] at h
        exact (not_le.mpr h_lt) h
      | inr h_le => exact h_le
  · intro h
    rw [if_neg (not_lt.mpr h)]
    rfl

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

theorem zero_truncatedAdd (i : I) : truncatedAdd 0 i = i := by
  simp only [truncatedAdd, coe_zero, zero_add, min_def]
  split
  case isTrue h => exact le_antisymm h le_one'
  case isFalse _ => rfl

theorem truncatedAdd_zero (i : I) : truncatedAdd i 0 = i := by
  simp only [truncatedAdd, coe_zero, add_zero, min_def]
  split
  case isTrue h => exact le_antisymm h le_one'
  case isFalse _ => rfl

theorem truncatedAdd_assoc (i j k : I) :
    truncatedAdd (truncatedAdd i j) k = truncatedAdd i ( truncatedAdd j k) := by
  simp only [truncatedAdd, min_def, Subtype.mk.injEq]
  split
  case isTrue h_ij =>
    rw [if_pos]
    pick_goal 2
    . calc (1:ℝ)
      _ = 1 + 0 := Eq.symm (AddLeftCancelMonoid.add_zero 1)
      _ ≤ 1 + k := add_le_add le_rfl nonneg'
    · split
      case isTrue h_jk =>
        rw [if_pos]
        calc (1:ℝ)
        _ = 0 + 1 := Eq.symm (AddLeftCancelMonoid.zero_add 1)
        _ ≤ i + 1 := add_le_add nonneg' le_rfl
      case isFalse h_jk =>
        rw [if_pos]
        rw [← add_assoc]
        calc (1:ℝ)
        _ = 1 + 0 := Eq.symm (AddLeftCancelMonoid.add_zero 1)
        _ ≤ i + j + k := add_le_add h_ij nonneg'
  case isFalse h_ij =>
    split
    case isTrue h_ijk =>
      split
      case isTrue h_jk =>
        rw [if_pos]
        calc (1:ℝ)
        _ = 0 + 1 := Eq.symm (AddLeftCancelMonoid.zero_add 1)
        _ ≤ i + 1 := add_le_add nonneg' le_rfl
      case isFalse h_jk =>
        rw [← add_assoc, if_pos h_ijk]
    case isFalse h_ijk =>
      split
      case isTrue h_jk =>
        exfalso
        rw [add_assoc] at h_ijk
        apply h_ijk
        calc (1:ℝ)
        _ = 0 + 1 := Eq.symm (AddLeftCancelMonoid.zero_add 1)
        _ ≤ i + (j + k) := add_le_add nonneg' h_jk
      case isFalse h_jk =>
        rw [← add_assoc, if_neg h_ijk]

theorem truncatedAdd_comm (i j : I) :
    (truncatedAdd i j) = truncatedAdd j i := by
  simp only [truncatedAdd, min_def, Subtype.mk.injEq]
  rw [add_comm]

theorem truncatedAdd_le_truncatedAdd_left (i j : I) (h_le : i ≤ j) :
    ∀ k, truncatedAdd k i ≤ truncatedAdd k j := by
  intro k
  unfold truncatedAdd
  rw [Subtype.mk_le_mk] at h_le
  simp only [min_def, Subtype.mk_le_mk]
  split
  case isTrue h_ki =>
    rw [if_pos]
    calc (1:ℝ)
    _ ≤ k + i := h_ki
    _ ≤ k + j := (add_le_add_iff_left ↑k).mpr h_le
  case isFalse h_ki =>
    rw [not_le] at h_ki
    split
    case isTrue h_kj =>
      exact le_of_lt h_ki
    case isFalse h_kj =>
      exact (add_le_add_iff_left ↑k).mpr h_le


noncomputable instance : Add unitInterval where
  add := truncatedAdd

noncomputable instance : OrderedAddCommMonoid unitInterval where
  add_assoc := truncatedAdd_assoc
  add_comm := truncatedAdd_comm
  zero_add := zero_truncatedAdd
  add_zero := truncatedAdd_zero
  nsmul := nsmulRec
  add_le_add_left := truncatedAdd_le_truncatedAdd_left

theorem unitInterval_summable (f : α → I) : Summable I := by sorry

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
