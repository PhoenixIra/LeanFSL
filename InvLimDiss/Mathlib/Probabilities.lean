import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Rify
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.Field.Defs

/-!
# Extended unitInterval

This file contains lemmas and definitions used in conjunction with unitInterval.
We usually interpret the unitInterval as probabilities.

This file is features the following content:
* `unit_cl` as an instantionation of a CompleteLinearOrder on the unitInterval
* Section `MulDiv` featuring the truncated division (truncated to 1) and various lemmas of multiplication and truncated division on the unitInterval
* Section `Symm` featuring lemmas about the symmetrie on the unitInterval, i.e. 1-x
* Section `Ite` featuring definitions for quantitative if then else expressions, especially iverson brackets, i.e. if then else to one and zero, here called `IteZeroOne` and respective lemmas.
* Section `AddSub` featuring truncated add (truncated to 1) and truncated sub (truncated to 0), lemmas involving them as well as lemmas around infinite additions, especially their existence.
* Section `Quantifiers` featuring additional theorems about infimum and supremum
-/


namespace unitInterval

open Classical Set.Icc

/--
The unitInterval forms a complete lattice with a linear order.
-/
instance : Fact ((0:Real) ≤ 1) := by constructor; exact zero_le_one
noncomputable instance unit_cl : CompleteLinearOrder I := instCompleteLinearOrderElemIccOfFactLe

theorem unit_top_eq_one : (⊤ : I) = (1 : I) := rfl

theorem unit_bot_eq_zero : (⊥ : I) = (0 : I) := rfl

/-!
  This section includes the following content:
  * Prove that multiplication is monotone. The typeclasses we prove suggest using `OrderedSemiring`.
  However, the unitInterval is not an `OrderedSemiring`.
  * Various lemmas about multiplication on the unit interval
  * The truncated division `unitDiv` as well as lemmas about its use
-/
section MulDiv

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

lemma unit_mul_comm (i j : I) : i * j = j * i := by
  rw [Subtype.mk_eq_mk, coe_mul, coe_mul]
  exact mul_comm (i:ℝ) (j:ℝ)

theorem unit_mul_le_mul {i₁ i₂ j₁ j₂ : I} (h_i : i₁ ≤ i₂) (h_j : j₁ ≤ j₂) : i₁ * j₁ ≤ i₂ * j₂ := by
  apply mul_le_mul
  · exact h_i
  · exact h_j
  · exact nonneg'
  · exact nonneg'

instance : MulZeroClass I where
  zero_mul i := by rw [Subtype.mk_eq_mk, coe_mul]; exact zero_mul (i:ℝ)
  mul_zero i := by rw [unit_mul_comm]; exact zero_mul i

instance : MulOneClass I where
  one_mul i := by rw[Subtype.mk_eq_mk, coe_mul]; exact one_mul (i:ℝ)
  mul_one i := by rw [unit_mul_comm]; exact one_mul i

-- instance : CancelMonoidWithZero I := by infer_instance

lemma div_le_one {a b : ℝ} (h_b_pos : 0 < b) (h_ab : a ≤ b): a/b ≤ 1 := by
  have h_b_nonneg : 0 ≤ b := by apply le_iff_lt_or_eq.mpr; left; exact h_b_pos
  have : b ≤ b := by apply le_iff_lt_or_eq.mpr; right; rfl
  calc a / b ≤ b / b    := by exact (div_le_div₀ h_b_nonneg h_ab h_b_pos this)
           _ = 1        := (div_eq_one_iff_eq (ne_of_gt h_b_pos)).mpr rfl

lemma div_mem_unit {a b : ℝ} (h_a_nonneg : 0 ≤ a) (h_ab : a < b): a/b ∈ I := by
  have h_b_pos: 0 < b := by apply lt_of_le_of_lt; exact h_a_nonneg; exact h_ab
  simp; apply And.intro;
  · exact div_nonneg h_a_nonneg (le_of_lt h_b_pos)
  · exact div_le_one h_b_pos (le_of_lt h_ab)

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
        apply div_le_div₀
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
        exact (le_div_iff₀ this).mp h_div
    case isFalse h_jk =>
      simp only [not_lt] at h_jk
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
        exact (le_div_iff₀ this).mpr h_mul
    case isFalse => exact le_one'

@[simp]
lemma unit_div_zero (i : I) : i / 0 = 1 := by
  rw [Subtype.mk_eq_mk, coe_div]
  simp only [coe_zero, div_zero, coe_one, ite_eq_right_iff, zero_ne_one, imp_false, not_lt]
  exact nonneg'

lemma zero_unit_div (i : I) (h : 0 < i) : 0 / i = 0 := by
  rw [Subtype.mk_eq_mk, coe_div]
  split_ifs
  simp only [coe_zero, zero_div]

lemma zero_unit_div_of_ne (i : I) (h : i ≠ 0) : 0 / i = 0 := by
  apply zero_unit_div
  exact lt_of_le_of_ne nonneg' (Ne.symm h)

@[simp]
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
  apply Iff.intro
  · rw [Subtype.mk_eq_mk, coe_div]
    intro h
    simp only [coe_one, ite_eq_right_iff] at h
    cases eq_or_ne j 0 with
    | inl h_zero => rw [h_zero]; exact nonneg'
    | inr h_n_zero =>
      cases lt_or_le i j with
      | inl h_lt =>
        exfalso
        obtain h := le_of_eq (h h_lt).symm
        have : 0 < j := by {apply lt_of_le_of_ne nonneg' (Ne.symm h_n_zero)}
        rw [le_div_iff₀ this, one_mul, Subtype.coe_le_coe] at h
        exact (not_le.mpr h_lt) h
      | inr h_le => exact h_le
  · intro h
    exact unit_div_of_le h

-- @[norm_cast]
-- lemma coe_pos {x : I} : (0 : ℝ) < x ↔ 0 < x := Iff.rfl

-- @[norm_cast]
-- lemma coe_lt_one {x : I} : (x : ℝ) < 1 ↔ x < 1 := Iff.rfl

lemma ne_zero_iff_pos {x : I} : x ≠ 0 ↔ 0 < x := by
  rw [← coe_ne_zero, ← coe_pos, lt_iff_le_and_ne, and_iff_right (nonneg x), ne_comm]

lemma ne_one_iff_lt {x : I} : x ≠ 1 ↔ x < 1 := by
  rw [← coe_lt_one, ← coe_ne_one, lt_iff_le_and_ne, and_iff_right (le_one x)]

lemma mul_div_cancel_of_pos {i j : I} (h_nonzero : i ≠ 0) : j * i / i = j := by
  rw [Subtype.mk_eq_mk, coe_div, coe_mul]
  split
  case isTrue h =>
    have : i ≠ 0 := by intro h_i; rw[h_i] at h; simp only [mul_zero, lt_self_iff_false] at h
    rw [← mul_div, div_self]
    · simp only [mul_one]
    · simp only [ne_eq, coe_eq_zero, this, not_false_eq_true]
  case isFalse h =>
    contrapose! h
    simp only [ne_eq, ne_zero_iff_pos, ← coe_pos] at h_nonzero
    simp only [ne_eq, Eq.comm, coe_eq_one, ne_one_iff_lt, ← coe_lt_one] at h
    exact Subtype.coe_lt_coe.mp <| by simpa using mul_lt_mul_of_pos_right h h_nonzero

lemma div_mul_le_cancel {i j : I} : j / i * i ≤ j := by
  rw [Subtype.mk_le_mk, coe_mul, coe_div]
  split
  case isTrue h_ji =>
    have : (i : ℝ) ≠ 0 := by intro h; apply not_le.mpr h_ji; rw [Subtype.mk_le_mk, h]; exact nonneg'
    rw [div_mul, div_self this, div_one]
  case isFalse h_ij =>
    rw [not_lt] at h_ij
    rw [one_mul]
    exact h_ij

lemma div_swap {i j k : I} : i / j / k = i / k / j := by
  apply le_antisymm
  <;> {
    rw [unit_le_div_iff_mul_le, unit_le_div_iff_mul_le]
    rw [mul_assoc]; nth_rw 2 [mul_comm]; rw [← mul_assoc]
    rw [← unit_le_div_iff_mul_le, ← unit_le_div_iff_mul_le]
  }

lemma div_mul_eq_div_div {i j k : I} : i / (j * k) = i / j / k := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_div, coe_mul]
  split_ifs
  case pos => rw [div_div]
  case neg h_i_jk h_ij_k h_j_i =>
    exfalso
    apply h_j_i
    apply lt_of_lt_of_le h_i_jk
    exact mul_le_left
  case neg h_i_jk h_k_ij =>
    exfalso
    apply h_k_ij
    rw [Subtype.mk_lt_mk, coe_div]
    split_ifs
    case pos h_i_j =>
      have h_j_pos : 0 < (j : ℝ) := by {
        apply lt_of_le_of_lt nonneg' h_i_j
      }
      rw [div_lt_iff₀ h_j_pos, mul_comm]
      exact h_i_jk
    case neg h_j_i =>
      exfalso
      rw [not_lt] at h_j_i
      have := lt_of_le_of_lt h_j_i h_i_jk
      rw [← not_le] at this
      exact this mul_le_left
  case pos h_jk_i h_ij_k h_i_j =>
    exfalso
    simp only [not_lt] at h_jk_i
    rw [Subtype.mk_lt_mk, coe_div] at h_ij_k
    split_ifs at h_ij_k
    have h_j_pos : 0 < j := lt_of_le_of_lt nonneg' h_i_j
    rw [div_lt_iff₀ h_j_pos] at h_ij_k
    rw [Subtype.mk_le_mk] at h_jk_i
    have := lt_of_le_of_lt h_jk_i h_ij_k
    rw [coe_mul, mul_comm, ← not_le] at this
    apply this
    rfl
  case neg h_jk_i h_ij_k h_j_i =>
    exfalso
    rw [Subtype.mk_lt_mk, coe_div] at h_ij_k
    split_ifs at h_ij_k
    rw [← not_le] at h_ij_k
    exact h_ij_k le_one'
  case neg => rfl

theorem unit_mul_div {i j k : I} : i * (j / k) ≤ i * j / k := by
  rw [Subtype.mk_le_mk]
  simp only [coe_mul, coe_div, mul_ite, mul_one]
  split_ifs
  case pos h_jk h_ijk =>
    rw [mul_div (i : ℝ) j k]
  case neg h_jk h_kij =>
    exfalso
    apply h_kij
    apply lt_of_le_of_lt ?_ h_jk
    exact mul_le_right
  case pos h_kj h_ijk =>
    rw [not_lt, Subtype.mk_le_mk] at h_kj
    rw [← mul_div]
    rw [← one_le_div (lt_of_le_of_lt nonneg' h_ijk)] at h_kj
    apply le_trans ?_ <| mul_le_mul le_rfl h_kj zero_le_one nonneg'
    simp only [mul_one, le_refl]
  case neg => exact le_one'

theorem mul_iInf [Nonempty α] {i : I} {j : α → I} : i * ⨅ a : α, j a = ⨅ a : α, i * j a := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_mul, zero_le_one, coe_iInf]
  rw [Real.mul_iInf_of_nonneg nonneg']

end MulDiv

/-!
  Thie section contains lemmas about the symmetrie, written here as `σ`, but usually refered to as 1-x.
-/
section Symm

@[simp]
lemma eq_zero_iff_sym_eq_one : σ x = 1 ↔ x = 0 := by
  apply Iff.intro
  · intro h
    rw [← unitInterval.symm_zero] at h
    exact symm_bijective.injective h
  · intro h
    rw [h]
    exact symm_zero

@[simp]
lemma eq_one_iff_sym_eq_zero : σ x = 0 ↔ x = 1 := by
  apply Iff.intro
  · intro h
    rw [← unitInterval.symm_one] at h
    exact symm_bijective.injective h
  · intro h
    rw [h]
    exact symm_one

theorem le_symm_if_le_symm (i j : I) : i ≤ σ j → j ≤ σ i := by
  intro h
  rw [Subtype.mk_le_mk, coe_symm_eq] at h ⊢
  apply le_sub_left_of_add_le
  rw [add_comm]
  apply add_le_of_le_sub_left
  exact h

theorem le_symm_iff_le_symm (i j : I) : i ≤ σ j ↔ j ≤ σ i :=
  ⟨le_symm_if_le_symm i j, le_symm_if_le_symm j i⟩

theorem symm_le_if_symm_le (i j : I) : σ i ≤ j → σ j ≤ i := by
  intro h
  rw [Subtype.mk_le_mk, coe_symm_eq] at h ⊢
  rw [sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add]
  exact h

theorem symm_le_iff_symm_le (i j : I) : σ i ≤ j ↔ σ j ≤ i :=
  ⟨symm_le_if_symm_le i j, symm_le_if_symm_le j i⟩

theorem lt_symm_if_lt_symm (i j : I) : i < σ j → j < σ i := by
  intro h
  rw [Subtype.mk_lt_mk, coe_symm_eq] at h ⊢
  apply lt_sub_left_of_add_lt
  rw [add_comm]
  apply add_lt_of_lt_sub_left
  exact h

theorem lt_symm_iff_lt_symm (i j : I) : i < σ j ↔ j < σ i :=
  ⟨lt_symm_if_lt_symm i j, lt_symm_if_lt_symm j i⟩

theorem symm_lt_if_symm_lt (i j : I) : σ i < j → σ j < i := by
  intro h
  rw [Subtype.mk_lt_mk, coe_symm_eq] at h ⊢
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact h

theorem symm_lt_iff_symm_lt (i j : I) : σ i < j ↔ σ j < i :=
  ⟨symm_lt_if_symm_lt i j, symm_lt_if_symm_lt j i⟩

@[simp]
theorem symm_eq_symm_iff_eq (i j : I) : σ i = σ j ↔ i = j := by
  apply Iff.intro
  · intro h
    rw [Subtype.mk_eq_mk, coe_symm_eq, coe_symm_eq] at h
    simp only [sub_right_inj] at h
    exact Subtype.mk_eq_mk.mpr h
  · intro h
    rw [h]


end Symm

/-! This section contains if then else on the unit interval, especially if the result is either 1 or 0,
  in which case we call it `iteOneZero`. We do not define fancy syntax for this but use it as is.
  We also have lemmas about the usage of `iteOneZero`. -/
section Ite

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

lemma iteOneZero_le {P : Prop} {i : I} :
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

@[simp]
lemma sym_iteOneZero_eq {P : Prop} :
    σ (iteOneZero P) = iteOneZero (¬ P) := by
  simp only [iteOneZero_eq_ite]
  split_ifs
  case pos => exact symm_one
  case neg => exact symm_zero

lemma iteOneZero_mul_iteOneZero_eq {P Q : Prop} :
    iteOneZero P * iteOneZero Q = iteOneZero (P ∧ Q) := by
  simp only [iteOneZero_eq_ite, mul_ite, mul_one, mul_zero]
  split_ifs
  case pos => rfl
  case neg h_Q h_P h => exfalso; apply h; exact ⟨h_P, h_Q⟩
  case pos h_Q h_P h => exfalso; apply h_P; exact h.left
  case neg => rfl
  case pos h_Q h => exfalso; apply h_Q; exact h.right
  case neg => rfl

lemma iteOneZero_mul_self {P : Prop} :
    iteOneZero P * iteOneZero P = iteOneZero P := by
  simp only [iteOneZero_eq_ite, mul_ite, mul_one, mul_zero, ite_eq_left_iff]
  intro h
  rw [if_neg h]

end Ite


/-!
  This section contains truncated addition and truncated subtraction:
  * The `truncatedAdd` operation, which truncated addition to 1 and lemmas about its use.
  * The adjoint `truncatedSub` operation, which truncated subtraction to 0.
  * A proof that `truncatedAdd` is an `CanonicallyOrderedAddCommMonoid`.
  * A proof that every funtion on the unit interval is summable `isSummable`.
-/
section AddSub

theorem truncatedAdd_mem_unit (i j : I) : min 1 ((i:ℝ) + j) ∈ I := by
  apply And.intro
  · exact le_min zero_le_one (add_nonneg i.property.1 j.property.1)
  · exact min_le_left 1 ((i:ℝ)+j)

noncomputable def truncatedAdd (i j : I) : I := ⟨min 1 (i + j), truncatedAdd_mem_unit i j⟩


noncomputable instance : Add unitInterval where
  add := truncatedAdd

theorem truncatedAdd_def {i j : I} : i + j = truncatedAdd i j := rfl

@[simp]
theorem coe_truncatedAdd {i j : I} : ↑(i + j) = min 1 ((i:ℝ) + j) := by
  conv => left; congr; rw [HAdd.hAdd, instHAdd, Add.add, instAddElemReal_invLimDiss]
  simp only
  rw [truncatedAdd]

theorem le_truncatedAdd (i j k : I) : i ≤ j + k ↔ i ≤ (j:ℝ) + k := by
  rw [Subtype.mk_le_mk, coe_truncatedAdd]
  apply Iff.intro
  · intro h
    simp only [le_min_iff] at h
    exact h.right
  · intro h
    simp only [le_min_iff]
    exact ⟨le_one', h⟩

theorem le_truncatedAdd_of_unit (i j k : I) : ((j:ℝ) + k ≤ 1 → i ≤ (j:ℝ) + k) → i ≤ j + k := by
  intro h
  rw [Subtype.mk_le_mk, coe_truncatedAdd]
  by_cases (j:ℝ)+k ≤ 1
  case pos h_unit =>
    apply le_min
    · exact le_one'
    · exact h h_unit
  case neg h_nunit =>
    simp only [not_le] at h_nunit
    rw [min_eq_left h_nunit.le]
    exact le_one'

@[simp]
theorem zero_truncatedAdd (i : I) : 0 + i = i := by
  rw [Subtype.mk_eq_mk, coe_truncatedAdd]
  simp only [coe_zero, zero_add, min_def]
  split
  case isTrue h => exact le_antisymm h le_one'
  case isFalse _ => rfl

@[simp]
theorem truncatedAdd_zero (i : I) : i + 0 = i := by
  rw [Subtype.mk_eq_mk, coe_truncatedAdd]
  simp only [coe_zero, add_zero, min_def]
  split
  case isTrue h => exact le_antisymm h le_one'
  case isFalse _ => rfl

@[simp]
theorem one_truncatedAdd (i : I) : 1 + i = 1 := by
  rw [Subtype.mk_eq_mk, coe_truncatedAdd]
  simp only [coe_one, min_def, le_add_iff_nonneg_right, ite_eq_left_iff, not_le, add_right_eq_self,
    coe_eq_zero]
  intro h
  exfalso
  exact (not_le.mpr h) nonneg'

@[simp]
theorem truncatedAdd_one (i : I) : i + 1 = 1 := by
  rw [Subtype.mk_eq_mk, coe_truncatedAdd]
  simp only [coe_one, min_def, le_add_iff_nonneg_left, ite_eq_left_iff, not_le, add_left_eq_self,
    coe_eq_zero]
  intro h
  exfalso
  exact (not_le.mpr h) nonneg'

theorem truncatedAdd_assoc (i j k : I) :
    (i + j) + k = i + (j + k) := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_truncatedAdd, min_def, Subtype.mk.injEq]
  split
  case isTrue h_ij =>
    rw [if_pos]
    pick_goal 2
    · calc (1:ℝ)
      _ = 1 + 0 := Eq.symm (add_zero 1)
      _ ≤ 1 + k := add_le_add le_rfl nonneg'
    · split
      case isTrue h_jk =>
        rw [if_pos]
        calc (1:ℝ)
        _ = 0 + 1 := Eq.symm (zero_add 1)
        _ ≤ i + 1 := add_le_add nonneg' le_rfl
      case isFalse h_jk =>
        rw [if_pos]
        rw [← add_assoc]
        calc (1:ℝ)
        _ = 1 + 0 := Eq.symm (add_zero 1)
        _ ≤ i + j + k := add_le_add h_ij nonneg'
  case isFalse h_ij =>
    split
    case isTrue h_ijk =>
      split
      case isTrue h_jk =>
        rw [if_pos]
        calc (1:ℝ)
        _ = 0 + 1 := Eq.symm (zero_add 1)
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
        _ = 0 + 1 := Eq.symm (zero_add 1)
        _ ≤ i + (j + k) := add_le_add nonneg' h_jk
      case isFalse h_jk =>
        rw [← add_assoc, if_neg h_ijk]

theorem truncatedAdd_comm (i j : I) :
    i + j = j + i := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_truncatedAdd, min_def, Subtype.mk.injEq]
  rw [add_comm]

theorem truncatedAdd_le_truncatedAdd_left (i j : I) (h_le : i ≤ j) :
    ∀ k, k + i ≤ k + j := by
  intro k
  rw [Subtype.mk_le_mk] at h_le ⊢
  simp only [coe_truncatedAdd, le_min_iff, min_le_iff, le_refl, true_or, add_le_add_iff_left,
    Subtype.coe_le_coe, true_and]
  right
  exact h_le

theorem truncatedAdd_le_truncatedAdd (i₁ i₂ j₁ j₂ : I) (h_i : i₁ ≤ i₂) (h_j : j₁ ≤ j₂) :
    i₁ + j₁ ≤ i₂ + j₂ := by
  rw [Subtype.mk_le_mk] at h_i h_j ⊢
  simp only [coe_truncatedAdd, le_min_iff, min_le_iff, le_refl, true_or, true_and]
  right
  apply add_le_add h_i h_j

noncomputable instance : OrderedAddCommMonoid unitInterval where
  add_assoc := truncatedAdd_assoc
  add_comm := truncatedAdd_comm
  zero_add := zero_truncatedAdd
  add_zero := truncatedAdd_zero
  nsmul := nsmulRec
  add_le_add_left := truncatedAdd_le_truncatedAdd_left

theorem truncatedSub_mem_unitInterval {i j : I} : max 0 ((i:ℝ) - j) ∈ I := by
  simp only [Set.mem_Icc, le_max_iff, le_refl, sub_nonneg, Subtype.coe_le_coe, true_or, max_le_iff,
    zero_le_one, tsub_le_iff_right, true_and]
  calc (i:ℝ)
  _ ≤ 1 := le_one'
  _ = 1 + 0 := (add_zero 1).symm
  _ ≤ 1 + j := add_le_add le_rfl nonneg'

noncomputable def truncatedSub (i j : I) : I := ⟨max 0 ((i:ℝ) - j), truncatedSub_mem_unitInterval⟩

@[simp]
theorem coe_truncatedSub {i j : I} : ↑(truncatedSub i j) = max 0 ((i:ℝ) - j) := by
  rw [truncatedSub]

theorem add_truncatedSub {i j : I} (h : j ≤ i) : j + truncatedSub i j = i := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_truncatedAdd, coe_truncatedSub]
  rw [min_def, max_def]
  split
  case isTrue h_ij =>
    split
    case isTrue h_jij =>
      apply le_antisymm
      · rw [add_sub_cancel] at h_jij
        exact h_jij
      · exact le_one'
    case isFalse h_jij =>
      rw [add_sub_cancel]
  case isFalse h_ij =>
    simp only [sub_nonneg, Subtype.coe_le_coe] at h_ij
    exfalso
    exact h_ij h

theorem exists_truncatedAdd_of_le {i j : I} (h : i ≤ j) : ∃ k, j = i + k := by
  cases eq_or_ne i 1
  case inl h_eq =>
    rw [h_eq] at h ⊢
    have := le_antisymm le_one' h
    rw [this]
    use 0
    rw [Subtype.mk_eq_mk]
    simp only [coe_one, coe_truncatedAdd, coe_zero, add_zero, min_self]
  case inr h_ne =>
    use truncatedSub j i
    rw [add_truncatedSub h]

theorem le_self_truncatedAdd (i j : I) : i ≤ i + j := by
  rw [Subtype.mk_le_mk]
  simp only [coe_truncatedAdd, le_min_iff, le_add_iff_nonneg_right]
  exact ⟨le_one', nonneg'⟩

theorem le_truncatedAdd_iff_truncatedSub_le (i j k : I) :
    truncatedSub i j ≤ k ↔ i ≤ k + j := by
  apply Iff.intro
  · intro h
    rw [le_truncatedAdd]
    rw [Subtype.mk_le_mk, coe_truncatedSub, max_le_iff] at h
    obtain ⟨_, h⟩ := h
    linarith
  · intro h
    rw [Subtype.mk_le_mk, coe_truncatedSub, max_le_iff]
    rw [le_truncatedAdd] at h
    use nonneg'
    linarith

theorem iInf_add_le_add_iInf_of_antitone [LinearOrder ι] [Nonempty ι]
    {c₁ c₂ : ι → I} (h₁ : Antitone c₁) (h₂ : Antitone c₂) :
    ⨅ (i : ι), c₁ i + c₂ i ≤ (⨅ (i : ι), c₁ i) + ⨅ (i : ι), c₂ i := by
  rw [← le_truncatedAdd_iff_truncatedSub_le]
  apply le_iInf
  intro i₁
  rw [le_truncatedAdd_iff_truncatedSub_le, truncatedAdd_comm,
    ← le_truncatedAdd_iff_truncatedSub_le]
  apply le_iInf
  intro i₂
  rw [le_truncatedAdd_iff_truncatedSub_le, truncatedAdd_comm]
  apply iInf_le_of_le (max i₁ i₂)
  apply truncatedAdd_le_truncatedAdd
  · apply h₁
    apply le_max_left
  · apply h₂
    apply le_max_right

noncomputable instance : CanonicallyOrderedAdd unitInterval where
  exists_add_of_le := exists_truncatedAdd_of_le
  le_self_add := le_self_truncatedAdd

theorem hasSum (f : α → I) : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

theorem isSummable (f : α → I) : Summable f := ⟨_,hasSum f⟩

theorem iInf_finsetsum_le_finsetsum_iInf_of_antitone [LinearOrder ι] [Nonempty ι]
    {s : Finset α} { c : α → ι → I} (h : ∀ a, Antitone (c a)) :
    ⨅ (i : ι), ∑ (a ∈ s), c a i ≤ ∑ (a ∈ s), ⨅ (i : ι), c a i := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, ciInf_const, le_refl]
  | insert h_a ih =>
    rw [Finset.sum_insert h_a]
    conv => left; right; intro i; rw [Finset.sum_insert h_a]
    apply le_trans
    swap
    · apply truncatedAdd_le_truncatedAdd
      · exact le_rfl
      · exact ih
    · apply iInf_add_le_add_iInf_of_antitone
      · apply h
      · intro i₁ i₂ h_i
        simp only
        apply Finset.sum_le_sum
        intro a _
        exact h a h_i

theorem add_symm_mem_unitInterval_of_self (i j : I) : (i : ℝ) * j + (1 - (i : ℝ)) * j ∈ I := by
  rw [← right_distrib, add_sub_cancel, one_mul]
  exact j.prop

theorem add_symm_mem_unitInterval (i j k : I) : (i : ℝ) * j + (1 - i:ℝ) * k ∈ I := by
  wlog h_jk : j ≤ k
  · rw [not_le] at h_jk
    have h_jk := le_of_lt h_jk
    specialize this (σ i) k j h_jk
    rw [add_comm, symm, sub_sub_cancel] at this
    exact this
  · apply And.intro
    · have : (i : ℝ) * j + (1 - i:ℝ) * j ≤ (i : ℝ) * j + (1 - i:ℝ) * k := by {
        apply add_le_add
        · exact le_rfl
        · refine mul_le_mul le_rfl ?_ nonneg' (mem_iff_one_sub_mem.mp i.prop).left
          exact h_jk
      }
      refine le_trans ?_ this
      exact (add_symm_mem_unitInterval_of_self i j).left
    · have : (i : ℝ) * j + (1 - i:ℝ) * k ≤ (i : ℝ) * k + (1 - i:ℝ) * k := by {
        apply add_le_add
        · apply mul_le_mul le_rfl h_jk nonneg' nonneg'
        · exact le_rfl
      }
      apply le_trans this
      exact (add_symm_mem_unitInterval_of_self i k).right


theorem truncatedAdd_sym_mul_eq (i j : I) : i * j + σ i * j = j := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_truncatedAdd, coe_mul, coe_symm_eq]
  rw [min_eq_right_iff.mpr]
  · rw [← right_distrib, add_sub_cancel, one_mul]
  · exact (add_symm_mem_unitInterval i j j).right

theorem truncatedAdd_sym_eq (i : I) : i + σ i = 1 := by
  rw [← truncatedAdd_sym_mul_eq i 1]
  simp only [mul_one]

theorem weighted_is_unit (i j k : I) : (i * j : ℝ) + (σ i * k : ℝ) ≤ 1 := by
  simp only [coe_symm_eq]
  nth_rw 2 [← add_sub_cancel (i:ℝ) 1]
  apply add_le_add
  · exact mul_le_left
  · rw [← coe_symm_eq]
    exact mul_le_left

theorem right_distrib_of_unit (i j k : I) (h_unit : (i:ℝ) + (j:ℝ) ≤ 1) :
    (i + j) * k = i * k + j * k := by
  rw [Subtype.mk_eq_mk]
  simp only [coe_mul, coe_truncatedAdd]
  rw [min_eq_right_iff.mpr h_unit, ← right_distrib, min_eq_right_iff.mpr]
  exact mul_le_one₀ h_unit nonneg' le_one'

theorem left_distrib_of_unit (i j k : I) (h_unit : (i:ℝ) + (j:ℝ) ≤ 1) :
    k * (i + j) = k * i + k * j := by
  simp only [unit_mul_comm]
  rw [unit_mul_comm k (i + j)]
  exact right_distrib_of_unit i j k h_unit

theorem left_subdistr_of_unit (i j k : I) :
    i * (j + k) ≤ (i * j) + (i * k) := by
  simp only [le_truncatedAdd, coe_mul, coe_truncatedAdd, ← left_distrib]
  apply mul_le_mul le_rfl ?_ (truncatedAdd_mem_unit _ _).left nonneg'
  simp only [min_le_iff, le_refl, or_true]

theorem right_subdistr_of_unit (i j k : I) :
    (j + k) * i ≤ (j * i) + (k * i) := by
  rw [mul_comm]
  apply le_trans (left_subdistr_of_unit _ _ _)
  rw [mul_comm i j, mul_comm i k]

theorem superdistr_of_unit_div (i j k : I) :
    (j/i) + (k/i) ≤ (j + k) / i := by
  rw [unit_le_div_iff_mul_le]
  apply le_trans (right_subdistr_of_unit _ _ _)
  apply truncatedAdd_le_truncatedAdd
  · exact div_mul_le_cancel
  · exact div_mul_le_cancel

end AddSub

section Quantifier

instance : SMul I (Set I) where
  smul i s := {x | ∃ j ∈ s, x = i * j}

theorem hSMul_def (i : I) (s : Set I) : i • s = {x | ∃ j ∈ s, x = i * j} := rfl

theorem hSMul_emp (i : I) : i • (∅ : Set I) = ∅ := by
  simp only [hSMul_def, Set.mem_empty_iff_false, false_and, exists_const, Set.setOf_false]

theorem coe_sInf {s : Set I} (h : Set.Nonempty s) : (sInf s) = sInf (s : Set ℝ) := by
  rw [Set.Icc.coe_sInf]
  · exact zero_le_one' ℝ
  · exact h

open Pointwise in
theorem smul_real_eq_smul_unit (i : I) (s : Set I) :
    ((i : ℝ) • (Subtype.val '' s)) = ↑(i • s) := by
  apply Set.ext
  intro a
  apply Iff.intro
  · rintro ⟨_, ⟨j,h_s,rfl⟩, rfl⟩
    simp only
    use (i * j)
    refine And.intro ?_ rfl
    use j
  · rintro ⟨_,⟨j,h_s,rfl⟩,rfl⟩
    use j
    simp only
    refine And.intro ?_ rfl
    use j

theorem sInf_smul (a : I) (s : Set I) : a * sInf s ≤ sInf (a • s) := by
  cases eq_or_ne s ∅ with
  | inl h_emp => rw [h_emp, hSMul_emp,_root_.sInf_empty]; exact le_one'
  | inr h_nonempty =>
    rw [← Set.nonempty_iff_ne_empty] at h_nonempty
    rw [hSMul_def, Subtype.mk_le_mk, coe_mul, coe_sInf h_nonempty]
    rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg (nonneg a) (Subtype.val '' s)]
    rw [smul_real_eq_smul_unit]
    have : Set.Nonempty (a • s) := by {
      obtain ⟨x, h_x⟩ := h_nonempty
      use (a * x), x
    }
    rw [← coe_sInf this, Subtype.coe_le_coe]
    apply le_rfl

theorem sInf_smul_of_nonneg (a : I) {s : Set I} (h : s.Nonempty) :
    a * sInf s = sInf (a • s) := by
  apply le_antisymm
  · exact sInf_smul a s
  · rw [hSMul_def, Subtype.mk_le_mk, coe_mul, coe_sInf h]
    rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg (nonneg a) (Subtype.val '' s)]
    rw [smul_real_eq_smul_unit]
    have : Set.Nonempty (a • s) := by {
      obtain ⟨x, h_x⟩ := h
      use (a * x), x
    }
    rw [← coe_sInf this, Subtype.coe_le_coe]
    apply le_rfl

end Quantifier

end unitInterval
