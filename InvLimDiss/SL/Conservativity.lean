import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.QuantitativeProofrules


namespace QSL

variable {Var : Type}

open SL unitInterval

theorem conservative_true : `[qsl Var| qTrue] = `[qsl Var| ⁅`[sl Var| sTrue]⁆] := by
  apply funext
  intro _
  simp only [qslTrue, qslIverson, slTrue, unitInterval.iteOneZero_true]

theorem conservative_false : `[qsl Var| qFalse] = `[qsl Var| ⁅`[sl Var| sFalse]⁆] := by
  apply funext
  intro _
  simp only [qslFalse, qslIverson, slFalse, unitInterval.iteOneZero_false]

theorem conservative_emp : `[qsl Var| emp] = `[qsl Var| ⁅`[sl Var| emp]⁆] := by
  apply funext
  intro _
  simp only [qslEmp, qslIverson, slEmp]

theorem conservative_pointsTo : `[qsl Var| e ↦ e'] = `[qsl Var| ⁅`[sl Var| e ↦ e']⁆] := by
  apply funext
  intro _
  simp only [qslPointsTo, qslIverson, slPointsTo]

theorem conservative_equals : `[qsl Var| e = e'] = `[qsl Var| ⁅`[sl Var| e = e']⁆] := by
  apply funext
  intro _
  simp only [qslEquals, qslIverson, slEquals]

theorem conservative_subst (P : StateProp Var) :
    `[qsl Var| ⁅P⁆(v ↦ e)] = `[qsl Var| ⁅`[sl Var| [[P]](v ↦ e)]⁆] := by
  apply funext
  intro _
  simp only [qslSubst, qslIverson, slSubst]

theorem conservative_not (P : StateProp Var) :
    `[qsl Var| ~⁅P⁆] = `[qsl Var| ⁅`[sl Var| ¬ [[P]]]⁆] := by
  apply funext
  intro _
  simp only [qslNot, qslIverson, sym_iteOneZero_eq, slNot]

theorem conservative_min (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⊓ ⁅Q⁆] = `[qsl Var| ⁅`[sl Var| [[P]] ∧ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslMin, Inf.inf, qslIverson, iteOneZero_eq_iff, slAnd]
  split
  case isTrue h_p =>
    split
    case isTrue h_q =>
      simp only [ge_iff_le, le_refl, inf_of_le_left]
      rw [if_pos ⟨h_p, h_q⟩]
    case isFalse h_q =>
      simp only [ge_iff_le, zero_le, inf_of_le_right]
      rw [if_neg]
      simp only [h_q, and_false, not_false_eq_true]
  case isFalse h_q =>
    simp only [ge_iff_le, zero_le, inf_of_le_left]
    rw [if_neg]
    simp only [h_q, false_and, not_false_eq_true]

theorem conservative_max (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⊔ ⁅Q⁆] = `[qsl Var| ⁅`[sl Var| [[P]] ∨ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslMax, Sup.sup, qslIverson, iteOneZero_eq_iff, slOr]
  split
  case isTrue h_p =>
    rw [sup_of_le_left le_one', if_pos (Or.inl h_p)]
  case isFalse h_p =>
    split
    case isTrue h_q =>
      simp only [ge_iff_le, zero_le, sup_of_le_right]
      rw [if_pos (Or.inr h_q)]
    case isFalse h_q =>
      simp only [ge_iff_le, le_refl, sup_of_le_left]
      rw [if_neg]
      simp only [h_p, h_q, or_self, not_false_eq_true]

theorem conservative_add (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ + ⁅Q⁆] = `[qsl Var| ⁅`[sl Var| [[P]] ∨ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslAdd, Sup.sup, qslIverson, iteOneZero_eq_iff, slOr]
  split
  case isTrue h_p =>
    rw [one_truncatedAdd, if_pos]
    exact Or.inl h_p
  case isFalse h_p =>
    rw [zero_truncatedAdd]
    split
    case isTrue h_q =>
      rw [if_pos]
      exact Or.inr h_q
    case isFalse h_q =>
      rw [if_neg]
      simp only [h_p, h_q, or_self, not_false_eq_true]

theorem conservative_mul (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⬝ ⁅Q⁆] = `[qsl Var| ⁅`[sl Var| [[P]] ∧ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslMul, qslIverson, iteOneZero_eq_iff, mul_ite, mul_one, mul_zero, slAnd, Inf.inf]
  split
  case isTrue h_q =>
    split
    case isTrue h_p =>
      rw [if_pos ⟨h_p, h_q⟩]
    case isFalse h_p =>
      rw [if_neg]
      simp only [h_p, false_and, not_false_eq_true]
  case isFalse h_q =>
    rw [if_neg]
    simp only [h_q, and_false, not_false_eq_true]

theorem conservative_sup (P : α → StateProp Var) :
    `[qsl Var|S (x : α). ⁅P x⁆] = `[qsl Var| ⁅`[sl Var|∃ (x : α). [[P x]]]⁆] := by
  apply funext
  intro _
  simp only [qslSup, qslIverson, slExists, sSup, iSup_Prop_eq, Subtype.exists, exists_prop,
    iteOneZero_eq_iff]
  split
  case isTrue h =>
    rw [iSup_apply] at h
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := h
    apply le_antisymm
    · exact le_one'
    · rw [iSup_apply]
      apply le_trans ?_ (le_iSup _ a)
      simp only [qslIverson, h, iteOneZero_true, le_refl]
  case isFalse h =>
    rw [iSup_apply] at h
    simp only [iSup_Prop_eq, not_exists] at h
    apply le_antisymm
    · rw [iSup_apply]
      apply iSup_le
      intro a
      simp only [qslIverson, h a, iteOneZero_false, le_refl]
    · exact nonneg'

theorem conservative_inf (P : α → StateProp Var) :
    `[qsl Var|I (x : α). ⁅P x⁆] = `[qsl Var| ⁅`[sl Var|∀ (x : α). [[P x]]]⁆] := by
  apply funext
  intro _
  simp only [qslIverson, iteOneZero_eq_iff]
  split
  case isTrue h =>
    apply le_antisymm
    · exact le_one'
    · rw [qslInf_apply]
      rw [slAll_apply] at h
      apply le_iInf
      intro a
      simp only [qslIverson, h a, iteOneZero_true, le_refl]
  case isFalse h =>
    apply le_antisymm
    · rw [slAll_apply, not_forall] at h
      obtain ⟨a, h⟩ := h
      rw [qslInf_apply]
      apply le_trans (iInf_le _ a)
      simp only [qslIverson, h, iteOneZero_false, le_refl]
    · exact nonneg'

theorem conservative_sepMul (P Q : StateProp Var) :
    `[qsl Var|⁅P⁆ ⋆ ⁅Q⁆] = `[qsl Var| ⁅`[sl Var|[[P]] ∗ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslSepMul, qslIverson, iteOneZero_eq_iff, mul_ite, mul_one, mul_zero, slSepCon]
  split
  case isTrue h =>
    obtain ⟨heap₁, heap₂, h_p, h_q, h_disjoint, h_union⟩ := h
    apply le_antisymm
    · exact le_one'
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rw [if_pos h_q, if_pos h_p]
  case isFalse h =>
    simp only [not_exists, not_and] at h
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      split_ifs
      case pos h_q h_p =>
        exfalso
        exact h heap₁ heap₂ h_p h_q h_disjoint h_union
      case neg => rfl
      case neg => rfl
    · exact nonneg'

theorem conservative_bigSepMul (P : ℕ → StateProp Var) :
    `[qsl Var|[⋆] i ∈ { ... n}. ⁅P i⁆] = `[qsl Var| ⁅`[sl Var|[∗] i ∈ { ... n}. [[P i]]]⁆] := by
  induction n with
  | zero => simp only [qslBigSepMul, conservative_emp, slBigSepCon]
  | succ n ih => rw [qslBigSepMul, slBigSepCon, ih, conservative_sepMul]

theorem conservative_sepDiv (P Q : StateProp Var) :
    `[qsl Var|⁅P⁆ -⋆ ⁅Q⁆] = `[qsl Var| ⁅`[sl Var|[[P]] -∗ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [qslSepDiv, qslIverson, iteOneZero_eq_iff, slSepImp]
  split
  case isTrue h =>
    apply le_antisymm
    · exact le_one'
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      specialize h heap h_disjoint
      split_ifs
      case pos => simp only [unit_div_one, le_refl]
      case neg => simp only [unit_div_zero, le_refl]
      case pos h_q h_p => exfalso; exact h_q (h h_p)
      case neg => simp only [unit_div_zero, le_refl]
  case isFalse h =>
    simp only [not_forall, Classical.not_imp] at h
    obtain ⟨heap, h_disjoint, h_p, h_q⟩ := h
    apply le_antisymm
    · apply sInf_le
      use heap, h_disjoint
      rw [if_neg h_q, if_pos h_p]
      simp only [unit_div_one]
    · exact nonneg'

theorem qslIverson_eq_one (P : StateProp Var) :
    `[qsl Var| ⁅P⁆] s = 1 ↔ P s := by
  simp only [qslIverson, iteOneZero_eq_one_def]

end QSL
