import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.SL.QuantitativeProofrules


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
  simp only [fslMin, fslIverson, slAnd, iteOneZero_eq_ite]
  classical
  show _ = if P _ ⊓ Q _ then 1 else 0
  split
  case isTrue h =>
    obtain ⟨h_p, h_q⟩ := h
    show `[fsl| ⁅P⁆ ] _ ⊓ `[fsl| ⁅Q⁆ ] _ = 1
    simp only [fslIverson, iteOneZero_pos h_p, iteOneZero_pos h_q, min_self]
  case isFalse h =>
    simp only [inf_Prop_eq, not_and_or] at h
    show `[fsl| ⁅P⁆ ] _ ⊓ `[fsl| ⁅Q⁆ ] _ = 0
    cases h
    case inl h =>
      simp only [fslIverson, iteOneZero_neg h, zero_le, inf_of_le_left]
    case inr h =>
      simp only [fslIverson, iteOneZero_neg h, zero_le, inf_of_le_right]

theorem conservative_max (P Q : StateProp Var) :
    `[fsl Var| ⁅P⁆ ⊔ ⁅Q⁆] = `[fsl Var| ⁅`[sl Var| [[P]] ∨ [[Q]]]⁆] := by
  apply funext
  intro _
  show `[fsl| ⁅P⁆ ] _ ⊔ `[fsl| ⁅Q⁆ ] _ = _
  simp only [fslMax, Sup.sup, fslIverson, iteOneZero_eq_ite, slOr]
  classical
  show _ = if P _ ⊔ Q _ then 1 else 0
  split
  case isTrue h_p =>
    simp only [sup_Prop_eq]
    rw [sup_of_le_left le_one', if_pos (Or.inl h_p)]
  case isFalse h_p =>
    split
    case isTrue h_q =>
      simp only [zero_le, sup_of_le_right, sup_Prop_eq]
      rw [if_pos (Or.inr h_q)]
    case isFalse h_q =>
      simp only [max_self, sup_Prop_eq]
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
      show ¬(P _ ∨ Q _)
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
      show ¬(P _ ∧ Q _)
      simp only [h_p, false_and, not_false_eq_true]
  case isFalse h_q =>
    rw [if_neg]
    show ¬(P _ ∧ Q _)
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

namespace QSL

variable {Var : Type}

open SL ENNReal

theorem conservative_true : `[qsl Var| qTrue] s = 1 ↔ `[sl Var| sTrue] s := by
  simp only [qslTrue, slTrue]

theorem conservative_false : `[qsl Var| qFalse] s = 1 ↔ `[sl Var| sFalse] s := by
  simp only [qslFalse, zero_ne_one, slFalse, Bool.false_eq_true]

theorem conservative_emp : `[qsl Var| emp] s = 1 ↔ `[sl Var| emp] s := by
  simp only [qslEmp, iteOneZero_eq_one_def, slEmp]

theorem conservative_pointsTo : `[qsl Var| e ↦ e'] s = 1 ↔ `[sl Var| e ↦ e'] s := by
  simp only [qslPointsTo, iteOneZero_eq_one_def, slPointsTo]

theorem conservative_equals : `[qsl Var| e = e'] s = 1 ↔ `[sl Var| e = e'] s := by
  simp only [qslEquals, iteOneZero_eq_one_def, slEquals]

theorem conservative_disequals : `[qsl Var| e ≠ e'] s = 1 ↔ `[sl Var| ¬ e = e'] s := by
  simp only [qslDisEquals, ne_eq, iteOneZero_eq_one_def, slNot, slEquals]

theorem conservative_subst (P : StateProp Var) :
    `[qsl Var| ⁅P⁆(v ↦ e)] s = 1 ↔ `[sl Var| [[P]](v ↦ e)] s := by
  simp only [qslSubst, qslIverson, State.substituteStack, iteOneZero_eq_one_def, slSubst]

theorem conservative_min (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⊓ ⁅Q⁆] s = 1 ↔ `[sl Var| [[P]] ∧ [[Q]]] s := by
  simp only [qslMin, slAnd]
  show `[qsl| ⁅P⁆ ] s ⊓ `[qsl| ⁅Q⁆ ] s = 1 ↔ P s ⊓ Q s
  apply Iff.intro
  · intro h
    simp only [qslIverson, min_eq_iff, iteOneZero_eq_one_def] at h
    cases h
    case inl h =>
      rw [iteOneZero_pos h.left, one_le_iteOneZero] at h
      simp only [iteOneZero_eq_one_def, And.comm] at h
      exact h
    case inr h =>
      rw [iteOneZero_pos h.left, one_le_iteOneZero] at h
      simp only [iteOneZero_eq_one_def, And.comm] at h
      exact h
  · intro h
    simp only [Inf.inf, qslIverson, min_eq_iff] at h ⊢
    apply Or.inr
    simp only [h.right, iteOneZero_true, iteOneZero_pos h.left, le_refl, and_self]

theorem conservative_max (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⊔ ⁅Q⁆] s = 1 ↔ `[sl Var| [[P]] ∨ [[Q]]] s := by
  simp only [qslMax, slOr]
  show `[qsl| ⁅P⁆ ] s ⊔ `[qsl| ⁅Q⁆ ] s = 1 ↔ P s ⊔ Q s
  apply Iff.intro
  · intro h
    simp only [Sup.sup, qslIverson, max_eq_iff, iteOneZero_eq_one_def] at h
    cases h
    case inl h => exact Or.inl h.left
    case inr h => exact Or.inr h.left
  · intro h
    simp only [Sup.sup, qslIverson]
    cases h
    case inl h =>
      rw [iteOneZero_pos h, iteOneZero_eq_ite, max_eq_left_iff]
      split <;> simp only [le_refl, zero_le]
    case inr h =>
      rw [iteOneZero_pos h, iteOneZero_eq_ite, max_eq_right_iff]
      split <;> simp only [le_refl, zero_le]

theorem conservative_add (P Q : StateProp Var) :
    1 ≤ `[qsl Var| ⁅P⁆ + ⁅Q⁆] s ↔ `[sl Var| [[P]] ∨ [[Q]]] s := by
  simp only [qslAdd, slOr]
  apply Iff.intro
  · intro h
    simp only [qslIverson, iteOneZero_eq_ite] at h
    split_ifs at h
    <;> try {left; assumption} <;> try {right; assumption}
    simp only [add_zero, nonpos_iff_eq_zero, one_ne_zero] at h
  · intro h
    cases h
    case inl h => simp only [qslIverson, iteOneZero_pos h, self_le_add_right]
    case inr h => simp only [qslIverson, iteOneZero_pos h, self_le_add_left]

theorem conservative_mul (P Q : StateProp Var) :
    `[qsl Var| ⁅P⁆ ⬝ ⁅Q⁆] s = 1 ↔ `[sl Var| [[P]] ∧ [[Q]]] s := by
  simp only [qslMul, slAnd, qslIverson]
  apply Iff.intro
  · intro h
    simp only [iteOneZero_eq_ite, mul_ite, mul_one, mul_zero] at h
    split_ifs at h <;> try {constructor <;> assumption} <;> simp only [zero_ne_one] at h
  · intro h
    rw [iteOneZero_pos h.left, iteOneZero_pos h.right, mul_one]

theorem conservative_sup (P : α → StateProp Var) :
    `[qsl Var|S (x : α). ⁅P x⁆] s = 1 ↔ `[sl Var|∃ (x : α). [[P x]]] s := by
  simp only [qslSup, slExists]
  rw [iSup_apply, iSup_apply]
  apply Iff.intro
  · intro h
    rw [le_antisymm_iff] at h
    simp only [qslIverson, qslIverson, iteOneZero_eq_ite] at h
    obtain ⟨_, le_h⟩ := h
    contrapose! le_h
    simp only [iSup_Prop_eq, not_exists] at le_h
    rw [iSup_lt_iff]
    use 0
    simp only [zero_lt_one, nonpos_iff_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false, true_and]
    exact le_h
  · rintro ⟨P', ⟨i, h⟩, hP'⟩
    apply le_antisymm
    · apply iSup_le
      intro a
      simp only [qslIverson, iteOneZero_eq_ite]
      split <;> simp only [le_rfl, zero_le]
    · rw [le_iSup_iff]
      intro r h_r
      apply le_trans ?_ (h_r i); clear h_r r
      rw [qslIverson, iteOneZero_pos]
      simp only [eq_iff_iff] at h
      rw [h]
      exact hP'

theorem conservative_inf (P : α → StateProp Var) [h_nonempty : Nonempty α] :
    `[qsl Var|I (x : α). ⁅P x⁆] s = 1 ↔ `[sl Var|∀ (x : α). [[P x]]] s := by
  simp only [qslInf, slAll]
  apply Iff.intro
  · intro h P'
    simp only [Set.mem_range, eq_iff_iff, Subtype.exists, exists_prop, exists_exists_eq_and,
      forall_exists_index]
    intro a hP'
    rw [← hP']
    rw [le_antisymm_iff] at h
    obtain ⟨h_le, le_h⟩ := h
    contrapose! le_h
    rw [iInf_apply, iInf_lt_iff]
    use a
    simp only [qslIverson, iteOneZero_neg le_h, zero_lt_one]
  · intro h
    rw [iInf_apply] at h ⊢
    apply le_antisymm
    · have a := Classical.choice h_nonempty
      simp only [iInf_Prop_eq] at h
      specialize h a
      rw [iInf_le_iff]
      intro r h_r
      apply le_trans (h_r a)
      simp only [qslIverson, iteOneZero_pos h, le_refl]
    · apply le_iInf
      intro a
      simp only [iInf_Prop_eq] at h
      simp only [qslIverson, iteOneZero_pos (h a), le_refl]

theorem conservative_sepMul (P Q : StateProp Var) :
    `[qsl Var|⁅P⁆ ⋆ ⁅Q⁆] s =1 ↔ `[sl Var|[[P]] ∗ [[Q]]] s := by
  simp only [qslSepMul, qslIverson, iteOneZero_eq_ite, mul_ite, mul_one, mul_zero, slSepCon,
    exists_and_left]
  apply Iff.intro
  · intro h
    rw [le_antisymm_iff] at h
    obtain ⟨_, le_h⟩ := h
    contrapose le_h
    simp only [not_le]
    simp only [not_exists, not_and] at le_h
    apply lt_of_le_of_lt ?_ (zero_lt_one' ENNReal)
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    simp only [nonpos_iff_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hQ hP
    exact le_h heap₁ hP heap₂ hQ h_disjoint h_union
  · rintro ⟨heap₁, hP, heap₂, hQ, h_disjoint, h_union⟩
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨heap₁', heap₂', _, _, rfl⟩
      split_ifs <;> simp only [le_refl, zero_le]
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rw [if_pos hP, if_pos hQ]

theorem conservative_sepDiv (P Q : StateProp Var) :
    1 ≤ `[qsl Var|⁅P⁆ -⋆ ⁅Q⁆] s ↔ `[sl Var|[[P]] -∗ [[Q]]] s := by
  simp only [qslSepDiv, qslIverson, slSepImp]
  apply Iff.intro
  · intro h
    intro heap' h_disjoint hP
    contrapose! h
    apply lt_of_le_of_lt ?_ (zero_lt_one' ENNReal)
    apply sInf_le
    use heap', h_disjoint
    rw [iteOneZero_pos hP, iteOneZero_neg h]
    simp only [div'_one]
  · intro h
    apply le_sInf
    rintro _ ⟨heap', h_disjoint, rfl⟩
    specialize h heap' h_disjoint
    by_cases P ⟨s.stack, heap'⟩
    case pos hP =>
      specialize h hP
      rw [iteOneZero_pos hP, iteOneZero_pos h]
      simp only [div'_one, le_refl]
    case neg hnP =>
      rw [iteOneZero_neg hnP]
      simp only [div'_zero, le_top]

end QSL
