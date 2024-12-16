import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.ENNReal.Inv

namespace ENNReal

open Classical

noncomputable def ite_unit (P : Prop) (i j : ENNReal) : ENNReal := if P then i else j

lemma ite_unit_pos {P : Prop} (i j : ENNReal) (h : P) : ite_unit P i j = i := by
  unfold ite_unit
  exact if_pos h

lemma ite_unit_neg {P : Prop} (i j : ENNReal) (h : ¬ P) : ite_unit P i j = j := by
  unfold ite_unit
  exact if_neg h

lemma ite_unit_self {P : Prop} (i : ENNReal) :
    ite_unit P i i = i := by
  simp only [ite_unit, ite_self]

lemma ite_unit_def_of_ne {P : Prop} {i j : ENNReal} (h_ne : i ≠ j):
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

noncomputable def iteOneZero (P : Prop) : ENNReal := ite_unit P 1 0

lemma iteOneZero_pos {P : Prop} (h : P) : iteOneZero P = 1 := by
  unfold iteOneZero
  exact ite_unit_pos 1 0 h

@[simp]
lemma iteOneZero_true : iteOneZero True = 1 := iteOneZero_pos True.intro

lemma iteOneZero_neg {P : Prop} (h : ¬P) : iteOneZero P = 0 := by
  unfold iteOneZero
  exact ite_unit_neg 1 0 h

@[simp]
lemma iteOneZero_false : iteOneZero False = 0 := iteOneZero_neg (fun h => h.elim)

@[simp]
lemma iteOneZero_eq_one_def {P : Prop} : iteOneZero P = 1 ↔ P := by
  unfold iteOneZero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).1

@[simp]
lemma iteOneZero_eq_zero_def {P : Prop} : iteOneZero P = 0 ↔ ¬ P := by
  unfold iteOneZero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).2

lemma iteOneZero_eq_ite {P : Prop} : iteOneZero P = if P then 1 else 0 := rfl

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

lemma iteOneZero_eq_iteOneZero_iff {P Q : Prop} :
    iteOneZero P = iteOneZero Q ↔ (P ↔ Q) := by
  apply Iff.intro
  · intro h
    apply Iff.intro
    · intro hp; rw [iteOneZero_pos hp, Eq.comm, iteOneZero_eq_one_def] at h; exact h
    · intro hq; rw [iteOneZero_pos hq, iteOneZero_eq_one_def] at h; exact h
  · intro h
    rw [iteOneZero_eq_ite]
    split
    case isTrue hp => rw [Eq.comm, iteOneZero_eq_one_def]; exact h.mp hp
    case isFalse hnp => rw [Eq.comm, iteOneZero_eq_zero_def]; exact (not_iff_not.mpr h).mp hnp

lemma iteOneZero_le {P : Prop} {i : ENNReal} :
    iteOneZero P ≤ i ↔ (P → 1 ≤ i) := by
  apply Iff.intro
  · intro h_ite h_P
    rw [← iteOneZero_pos h_P]
    exact h_ite
  · intro h_imp
    rw [iteOneZero_eq_ite]
    split
    case isTrue h_P => exact h_imp h_P
    case isFalse => exact bot_le

lemma one_le_iteOneZero {P : Prop} :
    1 ≤ iteOneZero P ↔ iteOneZero P = 1 := by
  simp only [iteOneZero, ite_unit, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
  split
  case isTrue h => simp only [le_refl, h]
  case isFalse h => simp only [nonpos_iff_eq_zero, one_ne_zero, h]

lemma iteOneZero_mul_self {P : Prop} :
    iteOneZero P * iteOneZero P = iteOneZero P := by
  simp only [iteOneZero_eq_ite, mul_ite, mul_one, mul_zero, ite_eq_left_iff]
  intro h
  rw [if_neg h]

theorem ennreal_mul_le_mul {a b c d : ENNReal} (h_ab : a ≤ b) (h_cd : c ≤ d) : a * c ≤ b * d := by
  apply le_trans (mul_le_mul_left' h_cd _)
  exact mul_le_mul_right' h_ab _

noncomputable def div' (a b : ENNReal) : ENNReal := if b = 0 then ∞ else (if a = ∞ then ∞ else a / b)

theorem div'_le_div' {a b c d : ENNReal} (h_ab : a ≤ b) (h_dc : d ≤ c) : div' a c ≤ div' b d := by
  unfold div'
  split_ifs <;> (try rfl)
  case neg h_c h_d h_b =>
    exfalso
    apply h_d
    apply le_antisymm ?_ (zero_le d)
    apply le_trans h_dc
    rw [h_c]
  case neg h_c h_a h_d h_b =>
    exfalso
    apply h_b
    apply le_antisymm (OrderTop.le_top b)
    apply le_trans ?_ h_ab
    rw [h_a]
  case pos => exact OrderTop.le_top (a / c)
  case pos => exact OrderTop.le_top (a / c)
  case neg => exact ENNReal.div_le_div h_ab h_dc

theorem le_div'_iff_mul_le {a b c : ENNReal} : a ≤ b.div' c ↔ a * c ≤ b := by
  unfold div'
  split_ifs
  case pos h_c =>
    apply Iff.intro
    · simp only [le_top, h_c, mul_zero, zero_le, imp_self]
    · simp only [le_top, implies_true]
  case pos h_c h_b =>
    apply Iff.intro
    · simp only [le_top, h_b, imp_self]
    · simp only [le_top, implies_true]
  case neg h_c h_b =>
    exact ENNReal.le_div_iff_mul_le (Or.inl h_c) (Or.inr h_b)

@[simp]
lemma div'_one (i : ENNReal) : i.div' 1 = i := by
  unfold div'
  split_ifs
  case pos h => simp only [one_ne_zero] at h
  case pos h => rw [h]
  case neg h_i => exact div_one i

@[simp]
lemma div'_zero (i : ENNReal) : i.div' 0 = ∞ := by
  unfold div'
  rw [if_pos rfl]

theorem left_distr (i j k : ENNReal) :
    i * (j + k) = (i * j) + (i * k) := by
  cases i
  case top =>
    cases eq_or_ne j 0
    case inl h => simp only [h, zero_add, mul_zero]
    case inr h =>
      rw [ENNReal.top_mul h]
      rw [top_add]
      have : j+k ≠ 0 := by simp only [ne_eq, add_eq_zero, not_and]; intro h'; exact (h h').elim
      rw [ENNReal.top_mul this]
  case coe i =>
    cases j
    case top =>
      rw [top_add]
      cases eq_or_ne (i:ENNReal) 0
      case inl h_i => simp only [h_i, coe_zero, zero_mul, add_zero]
      case inr h_i => simp only [ENNReal.mul_top h_i, top_add]
    case coe j =>
      cases k
      case top =>
        simp only [add_top]
        cases eq_or_ne (i:ENNReal) 0
        case inl h_i => simp only [h_i, zero_mul, add_zero]
        case inr h_i => simp only [ENNReal.mul_top h_i, add_top]
      case coe k =>
        norm_cast
        rw [← NNReal.coe_inj]
        simp only [NNReal.coe_mul, NNReal.coe_add]
        rw [left_distrib]


end ENNReal
