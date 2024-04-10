import Mathlib.Topology.UnitInterval

namespace unitInterval

open Classical

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

noncomputable def ite_one_zero (P : Prop) : I := ite_unit P 1 0

lemma ite_one_zero_pos {P : Prop} (h : P) : ite_one_zero P = 1 := by
  unfold ite_one_zero
  exact ite_unit_pos 1 0 h

lemma ite_one_zero_neg {P : Prop} (h : ¬P) : ite_one_zero P = 0 := by
  unfold ite_one_zero
  exact ite_unit_neg 1 0 h

lemma ite_one_def {P : Prop} : ite_one_zero P = 1 ↔ P := by
  unfold ite_one_zero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).1

lemma ite_zero_def {P : Prop} : ite_one_zero P = 0 ↔ ¬ P := by
  unfold ite_one_zero
  exact (ite_unit_def_of_ne <| Ne.symm zero_ne_one).2

end unitInterval
