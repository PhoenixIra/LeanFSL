import Mathlib.Topology.UnitInterval

namespace unitInterval

open Classical

noncomputable def ite_unit (P : Prop) (i j : I) : I := if P then i else j

lemma ite_unit_pos {P : Prop} {i j : I} (h : P) : ite_unit P i j = i := by
  unfold ite_unit
  exact if_pos h

lemma ite_unit_neg {P : Prop} {i j : I} (h : ¬ P) : ite_unit P i j = j := by
  unfold ite_unit
  exact if_neg h

lemma ite_unit_def {P : Prop} {i j : I} : P ∧ ite_unit P i j = i ∨ ¬ P ∧ ite_unit P i j = j := by
  by_cases h : P
  · apply Or.inl
    apply And.intro h
    exact ite_unit_pos h
  · apply Or.inr
    apply And.intro h
    exact ite_unit_neg h

noncomputable def ite_one_zero (P : Prop) : I := ite_unit P 1 0

lemma ite_one_zero_pos {P : Prop} (h : P) : ite_one_zero P = 1 := by
  unfold ite_one_zero
  exact ite_unit_pos h

lemma ite_one_zero_neg {P : Prop} (h : ¬P) : ite_one_zero P = 0 := by
  unfold ite_one_zero
  exact ite_unit_neg h

lemma ite_one_zero_def {P : Prop} : P ∧ ite_one_zero P = 1 ∨ ¬ P ∧ ite_one_zero P = 0 := by
  unfold ite_one_zero
  exact ite_unit_def

end unitInterval
