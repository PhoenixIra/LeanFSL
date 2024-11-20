import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.FuzzyProofrules


namespace FSL

variable {Var : Type}

open SL unitInterval

theorem conservative_true : `[fsl Var| fTrue] = `[fsl Var| ⁅`[sl Var| sTrue]⁆] := by
  apply funext
  intro _
  simp only [fslTrue, fslIverson, slTrue, unitInterval.iteOneZero_true]

theorem conservative_false : `[fsl Var| fFalse] = `[fsl Var| ⁅`[sl Var| sFalse]⁆] := by
  apply funext
  intro _
  simp only [fslFalse, fslIverson, slFalse, Bool.false_eq_true, iteOneZero_false]

theorem conservative_emp : `[fsl Var| emp] = `[fsl Var| ⁅`[sl Var| emp]⁆] := by
  apply funext
  intro _
  simp only [fslEmp, fslIverson, slEmp]

theorem conservative_pointsTo : `[fsl Var| e ↦ e'] = `[fsl Var| ⁅`[sl Var| e ↦ e']⁆] := by
  apply funext
  intro _
  simp only [fslPointsTo, fslIverson, slPointsTo]

theorem conservative_equals : `[fsl Var| e = e'] = `[fsl Var| ⁅`[sl Var| e = e']⁆] := by
  apply funext
  intro _
  simp only [fslEquals, fslIverson, slEquals]

theorem conservative_subst (P : StateProp Var) :
    `[fsl Var| ⁅P⁆(v ↦ e)] = `[fsl Var| ⁅`[sl Var| [[P]](v ↦ e)]⁆] := by
  apply funext
  intro _
  simp only [fslSubst, fslIverson, slSubst]

theorem conservative_not (P : StateProp Var) :
    `[fsl Var| ~⁅P⁆] = `[fsl Var| ⁅`[sl Var| ¬ [[P]]]⁆] := by
  apply funext
  intro _
  simp only [fslNot, fslIverson, sym_iteOneZero_eq, slNot]

theorem conservative_min (P Q : StateProp Var) :
    `[fsl Var| ⁅P⁆ ⊓ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var| [[P]] ∧ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslMin, Inf.inf, fslIverson, iteOneZero_eq_ite, slAnd]
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
    `[fsl Var| ⁅P⁆ ⊔ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var| [[P]] ∨ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslMax, Sup.sup, fslIverson, iteOneZero_eq_ite, slOr]
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
    `[fsl Var| ⁅P⁆ + ⁅Q⁆] = `[fsl Var| ⁅`[sl Var| [[P]] ∨ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslAdd, Sup.sup, fslIverson, iteOneZero_eq_ite, slOr]
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
    `[fsl Var| ⁅P⁆ ⬝ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var| [[P]] ∧ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslMul, fslIverson, iteOneZero_eq_ite, mul_ite, mul_one, mul_zero, slAnd, Inf.inf]
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
    `[fsl Var|S (x : α). ⁅P x⁆] = `[fsl Var| ⁅`[sl Var|∃ (x : α). [[P x]]]⁆] := by
  apply funext
  intro _
  simp only [fslSup, fslIverson, slExists, sSup, iSup_Prop_eq, Subtype.exists, exists_prop,
    iteOneZero_eq_ite]
  split
  case isTrue h =>
    rw [iSup_apply] at h
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := h
    apply le_antisymm
    · exact le_one'
    · rw [iSup_apply]
      apply le_trans ?_ (le_iSup _ a)
      simp only [fslIverson, h, iteOneZero_true, le_refl]
  case isFalse h =>
    rw [iSup_apply] at h
    simp only [iSup_Prop_eq, not_exists] at h
    apply le_antisymm
    · rw [iSup_apply]
      apply iSup_le
      intro a
      simp only [fslIverson, h a, iteOneZero_false, le_refl]
    · exact nonneg'

theorem conservative_inf (P : α → StateProp Var) :
    `[fsl Var|I (x : α). ⁅P x⁆] = `[fsl Var| ⁅`[sl Var|∀ (x : α). [[P x]]]⁆] := by
  apply funext
  intro _
  simp only [fslIverson, iteOneZero_eq_ite]
  split
  case isTrue h =>
    apply le_antisymm
    · exact le_one'
    · rw [fslInf_apply]
      rw [slAll_apply] at h
      apply le_iInf
      intro a
      simp only [fslIverson, h a, iteOneZero_true, le_refl]
  case isFalse h =>
    apply le_antisymm
    · rw [slAll_apply, not_forall] at h
      obtain ⟨a, h⟩ := h
      rw [fslInf_apply]
      apply le_trans (iInf_le _ a)
      simp only [fslIverson, h, iteOneZero_false, le_refl]
    · exact nonneg'

theorem conservative_sepMul (P Q : StateProp Var) :
    `[fsl Var|⁅P⁆ ⋆ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var|[[P]] ∗ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslSepMul, fslIverson, iteOneZero_eq_ite, mul_ite, mul_one, mul_zero, slSepCon]
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
    `[fsl Var|[⋆] i ∈ { ... n}. ⁅P i⁆] = `[fsl Var| ⁅`[sl Var|[∗] i ∈ { ... n}. [[P i]]]⁆] := by
  induction n with
  | zero => simp only [fslBigSepMul, conservative_emp, slBigSepCon]
  | succ n ih => rw [fslBigSepMul, slBigSepCon, ih, conservative_sepMul]

theorem conservative_sepDiv (P Q : StateProp Var) :
    `[fsl Var|⁅P⁆ -⋆ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var|[[P]] -∗ [[Q]]]⁆] := by
  apply funext
  intro _
  simp only [fslSepDiv, fslIverson, iteOneZero_eq_ite, slSepImp]
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

theorem fslIverson_eq_one (P : StateProp Var) :
    `[fsl Var| ⁅P⁆] s = 1 ↔ P s := by
  simp only [fslIverson, iteOneZero_eq_one_def]

end FSL
