import InvLimDiss.SL.Quantitative

/-!
  This file features various lemmas involing quantitative separation logic on the unit Interval.
  Especially we have:
  * Simplification of Entailment relation
  * Theorems about separating operations like
     * Monotonicity
     * Adjointness
     * Vanishing Modus Ponens
     * Simplification lemmas
     * Distributivity over minimum and maximum
  * Eliminating theorems about quantifiers
-/

namespace QSL

open ENNReal State

variable {Var : Type}

section Entailment

theorem entailment_iff_pi_le {P Q : StateRVInf Var} : P ⊢ Q ↔ P ≤ Q := by rfl

theorem entailment_iff_le {P Q : StateRVInf Var} : P ⊢ Q ↔ ∀ s, P s ≤ Q s := by
  unfold Entailment.entail instEntailmentStateRVInf
  simp only
  rw [Pi.le_def]

end Entailment

/-! Proofrules for maxima and minima-/
section MaxMin

theorem qslMax_comm (P Q : StateRVInf Var) :
    `[qsl| [[P]] ⊔ [[Q]]] = `[qsl| [[Q]] ⊔ [[P]]] := by
  simp only [qslMax]
  exact sup_comm P Q

theorem qslMax_assoc (P Q R : StateRVInf Var) :
    `[qsl| ([[P]] ⊔ [[Q]]) ⊔ [[R]]] = `[qsl| [[P]] ⊔ [[Q]] ⊔ [[R]]] := by
  simp only [qslMax]
  exact sup_assoc P Q R

theorem qslMax_mono (P₁ P₂ Q₁ Q₂ : StateRVInf Var) (hP : P₁ ≤ P₂) (hQ : Q₁ ≤ Q₂) :
    `[qsl| [[P₁]] ⊔ [[Q₁]] ⊢ [[P₂]] ⊔ [[Q₂]]] := by
  simp only [qslMax, sup_le_iff]
  exact ⟨le_sup_of_le_left hP, le_sup_of_le_right hQ⟩

theorem qslMin_comm (P Q : StateRVInf Var) :
    `[qsl| [[P]] ⊓ [[Q]]] = `[qsl| [[Q]] ⊓ [[P]]] := by
  simp only [qslMin]
  exact inf_comm P Q

theorem qslMin_assoc (P Q R : StateRVInf Var) :
    `[qsl| ([[P]] ⊓ [[Q]]) ⊓ [[R]]] = `[qsl| [[P]] ⊓ [[Q]] ⊓ [[R]]] := by
  simp only [qslMin]
  exact inf_assoc P Q R

theorem qslMin_mono (P₁ P₂ Q₁ Q₂ : StateRVInf Var) (hP : P₁ ≤ P₂) (hQ : Q₁ ≤ Q₂) :
    `[qsl| [[P₁]] ⊓ [[Q₁]] ⊢ [[P₂]] ⊓ [[Q₂]]] := by
  simp only [qslMin, le_inf_iff]
  exact ⟨inf_le_of_left_le hP, inf_le_of_right_le hQ⟩

theorem qslMax_entailment_iff (P Q R : StateRVInf Var) :
    `[qsl| [[P]] ⊔ [[Q]] ⊢ [[R]]] ↔ P ⊢ R ∧ Q ⊢ R := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [qslMax] at h
      exact le_of_max_le_left h
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [qslMax] at h
      exact le_of_max_le_right h
  · rintro ⟨h_P, h_Q⟩
    intro s
    simp only [qslMax]
    exact max_le (h_P s) (h_Q s)


end MaxMin

section Arithmetic

theorem qslAdd_mono {P₁ P₂ Q₁ Q₂ : StateRVInf Var} :
    P₁ ⊢ P₂ → Q₁ ⊢ Q₂ → `[qsl| [[P₁]] + [[Q₁]] ⊢ [[P₂]] + [[Q₂]]] := by
  intro h_P h_Q s
  exact add_le_add (h_P s) (h_Q s)

theorem qslMul_mono {P₁ P₂ Q₁ Q₂ : StateRVInf Var} :
    P₁ ⊢ P₂ → Q₁ ⊢ Q₂ → `[qsl| [[P₁]] ⬝ [[Q₁]] ⊢ [[P₂]] ⬝ [[Q₂]]] := by
  intro h_P h_Q s
  exact ennreal_mul_le_mul (h_P s) (h_Q s)

theorem qslAdd_qslFalse (P : StateRVInf Var) :
    `[qsl| [[P]] + qFalse] = P := by
  funext s
  simp only [qslAdd, qslFalse, add_zero]

theorem qslMul_qslFalse (P : StateRVInf Var) :
    `[qsl| [[P]] ⬝ qFalse] = qslFalse := by
  funext s
  simp only [qslMul, qslFalse, mul_zero]

end Arithmetic

/-! This features elimination rules for quantifiers in fsl. -/
section Quantifiers

theorem qslSup_apply (P : α → StateRVInf Var) (s : State Var) :
    `[qsl| S x. [[P x]]] s = ⨆ x, P x s := by
  rw [qslSup, iSup_apply]

theorem qslInf_apply (P : α → StateRVInf Var) (s : State Var) :
    `[qsl| I x. [[P x]]] s = ⨅ x, P x s := by
  rw [qslInf, iInf_apply]

end Quantifiers

/-! We have here lemmas about separating multipication and division. -/
section Separating

theorem fslSepMul_mono {P₁ P₂ Q₁ Q₂ : StateRVInf Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
    `[qsl Var| [[P₁]] ⋆ [[Q₁]] ⊢ [[P₂]] ⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  apply le_sSup_iff.mpr
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro i h
  specialize h heap₁ heap₂ h_disjoint rfl rfl
  refine le_trans ?_ h; clear h
  apply ennreal_mul_le_mul
  · exact h_P ⟨s,heap₁⟩
  · exact h_Q ⟨s,heap₂⟩

theorem qslSepDiv_mono {P₁ P₂ Q₁ Q₂ : StateRVInf Var} (h_P : P₂ ⊢ P₁) (h_Q : Q₁ ⊢ Q₂) :
    `[qsl| [[P₁]] -⋆ [[Q₁]] ⊢ [[P₂]] -⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply le_sInf
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ h_disjoint rfl
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro _ h
  specialize h heap₁ h_disjoint rfl
  apply le_trans h
  apply div'_le_div'
  · exact h_Q ⟨s,heap ∪ heap₁⟩
  · exact h_P ⟨s,heap₁⟩

-- adjointness of sepcon and sepimp
theorem le_qslSepDiv_iff_qslSepMul_le (P₁ P₂ P₃ : StateRVInf Var) :
    `[qsl| [[P₁]] ⊢ [[P₂]] -⋆ [[P₃]]] ↔ `[qsl| [[P₁]] ⋆ [[P₂]] ⊢ [[P₃]]] := by
  apply Iff.intro
  case mp =>
    intro h ⟨s,heap⟩
    apply sSup_le
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₁ heap₂ h_disjoint rfl rfl
    rw [← (le_div'_iff_mul_le)]
    specialize h ⟨s,heap₁⟩
    unfold qslSepDiv at h
    simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h ((P₃ ⟨s,heap₁ ∪ heap₂⟩).div' (P₂ ⟨s,heap₂⟩)) heap₂ h_disjoint rfl
  case mpr =>
    intro h ⟨s,heap₁⟩
    apply le_sInf
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₂ h_disjoint rfl
    rw [ENNReal.le_div'_iff_mul_le]
    specialize h ⟨s,heap₁ ∪ heap₂⟩
    unfold qslSepMul at h
    rw [sSup_le_iff] at h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h (P₁ ⟨s,heap₁⟩ * P₂ ⟨s,heap₂⟩) heap₁ heap₂ h_disjoint rfl rfl

-- modus ponens of sepimp and sepcon
theorem qslSepMul_qslSepDiv_entail (P₁ P₂ : StateRVInf Var) :
    `[qsl| ([[P₁]] -⋆ [[P₂]]) ⋆ [[P₁]] ⊢ [[P₂]]] := by
  rintro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  cases eq_or_ne (P₁ ⟨s, heap₂⟩) 0
  case inl h_eq =>
    rw [h_eq, mul_zero]
    exact zero_le _
  case inr h_ne =>
    rw [← le_div'_iff_mul_le]
    apply sInf_le
    simp only [Set.mem_setOf_eq]
    exists heap₂

theorem qslSepMul_symm (f g : StateRVInf Var) : `[qsl| [[f]] ⋆ [[g]] ⊢ [[g]] ⋆ [[f]]] := by
  rw [Pi.le_def]
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  apply le_sSup
  use heap₂, heap₁
  rw [union_comm _ _ h_disjoint] at h_union
  rw [State.disjoint_comm] at h_disjoint
  use h_disjoint, h_union
  exact mul_comm _ _

theorem qslSepMul_comm (f g : StateRVInf Var) : `[qsl| [[f]] ⋆ [[g]]] = `[qsl| [[g]] ⋆ [[f]]] :=
  le_antisymm (qslSepMul_symm f g) (qslSepMul_symm g f)

theorem qslSepMul_assoc_le (f₁ f₂ f₃ : StateRVInf Var) :
    `[qsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]] ⊢ ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂₃, h_disjoint₁, h_union₁, rfl⟩
  rw [mul_comm, ← le_div'_iff_mul_le]
  apply sSup_le
  rintro _ ⟨heap₂, heap₃, h_disjoint₂₃, h_union₂₃, rfl⟩
  rw [le_div'_iff_mul_le]
  simp only at h_union₂₃
  rw [← h_union₂₃, disjoint_union_iff] at h_disjoint₁
  apply le_sSup_of_le
  · use (heap₁ ∪ heap₂), heap₃
    apply And.intro
    · rw [disjoint_comm _ _, disjoint_union_iff, disjoint_comm _ heap₁, disjoint_comm _ heap₂]
      exact ⟨h_disjoint₁.right, h_disjoint₂₃⟩
    · rw [← h_union₂₃, ← union_assoc] at h_union₁
      use h_union₁
  · rw [mul_assoc, mul_comm (f₃ _), ← mul_assoc, mul_comm (f₂ _)]
    refine ennreal_mul_le_mul ?_ le_rfl
    apply le_sSup
    use heap₁, heap₂, h_disjoint₁.left

theorem qslSepMul_assoc (f₁ f₂ f₃ : StateRVInf Var) :
    `[qsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]]] = `[qsl| ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
  apply le_antisymm
  · exact qslSepMul_assoc_le f₁ f₂ f₃
  · rw [qslSepMul_comm _ f₃, qslSepMul_comm f₁ _]
    rw [qslSepMul_comm f₁ _, qslSepMul_comm f₂ f₃]
    exact qslSepMul_assoc_le f₃ f₂ f₁

theorem qslEmp_qslSepDiv_eq (f : StateRVInf Var) : `[qsl| emp -⋆ [[f]]] = f := by
  funext s
  apply le_antisymm
  · apply sInf_le
    use ∅, disjoint_emptyHeap'
    simp only [union_emptyHeap, qslEmp, iteOneZero_true, div'_one]
  · apply le_sInf
    rintro _ ⟨heap, _, rfl⟩
    simp only [qslEmp, iteOneZero_eq_ite]
    split
    case isTrue h => rw [h, union_emptyHeap, div'_one]
    case isFalse h => rw [div'_zero]; exact le_top

theorem qslSepMul_qslEmp_eq (f : StateRVInf Var) : `[qsl| [[f]] ⋆ emp] = f := by
  funext s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
    simp only [qslEmp, iteOneZero_eq_ite, mul_ite, mul_one, mul_zero]
    split
    case isTrue h =>
      rw [h, union_emptyHeap] at h_union
      rw [h_union]
    case isFalse h => exact zero_le'
  · apply le_sSup
    use s.heap, ∅, disjoint_emptyHeap', union_emptyHeap'
    simp only [qslEmp, iteOneZero_true, mul_one]

theorem qslEmp_qslMul_qslSepMul_distr (f g : StateRVInf Var) :
    `[qsl| emp ⬝ ([[f]] ⋆ [[g]])] = `[qsl| (emp ⬝ [[f]]) ⋆ (emp ⬝ [[g]])] := by
  funext s
  apply le_antisymm
  · simp only [qslMul, qslEmp, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
    split
    case isTrue h_emp =>
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rw [← h_union, union_eq_emptyHeap_iff] at h_emp
      apply congrArg₂
      · simp only [qslMul, qslEmp, iteOneZero_pos h_emp.left, one_mul]
      · simp only [qslMul, qslEmp, iteOneZero_pos h_emp.right, one_mul]
    case isFalse => exact zero_le'
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    conv => right; rw [qslMul, qslEmp]
    simp only [iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
    split
    case isTrue h_emp =>
      rw [← h_union, union_eq_emptyHeap_iff] at h_emp
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      apply congrArg₂
      · simp only [qslMul, qslEmp, iteOneZero_pos h_emp.left, one_mul]
      · simp only [qslMul, qslEmp, iteOneZero_pos h_emp.right, one_mul]
    case isFalse h_n_emp =>
      simp only [qslMul, qslEmp, nonpos_iff_eq_zero, mul_eq_zero, iteOneZero_eq_zero_def]
      simp only [← h_union, union_eq_emptyHeap_iff, not_and_or] at h_n_emp
      cases h_n_emp
      case inl h₁ => left; left; exact h₁
      case inr h₂ => right; left; exact h₂

theorem qslSepMul_qslFalse_eq (f : StateRVInf Var) : `[qsl| [[f]] ⋆ qFalse] = `[qsl| qFalse] := by
  funext s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨_, _, _, _, rfl⟩
    simp only [qslFalse, mul_zero, le_refl]
  · simp only [qslFalse, zero_le]

theorem qslSepMul_qslMin_subdistr (P Q R : StateRVInf Var) :
    `[qsl| [[P]] ⋆ ([[Q]] ⊓ [[R]])] ≤ `[qsl| ([[P]] ⋆ [[Q]]) ⊓ ([[P]] ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  apply le_inf
  · apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply ennreal_mul_le_mul le_rfl ?_
      simp only [qslMin]
      show Q _ ⊓ R _ ≤ _
      rw [min_le_iff]
      left
      rfl
  · apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply ennreal_mul_le_mul le_rfl ?_
      simp only [qslMin]
      show Q _ ⊓ R _ ≤ _
      rw [min_le_iff]
      right
      rfl

theorem qslSepMul_qslMax_distr (P Q R : StateRVInf Var) :
    `[qsl| [[P]] ⋆ ([[Q]] ⊔ [[R]])] = `[qsl| ([[P]] ⋆ [[Q]]) ⊔ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_comm, ← le_div'_iff_mul_le]
    apply sup_le
    · rw [le_div'_iff_mul_le, mul_comm]
      simp only [qslMax]
      show _ ≤ `[qsl| [[P]] ⋆ [[Q]] ] s ⊔ `[qsl| [[P]] ⋆ [[R]] ] s
      rw [le_max_iff]
      left
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
    · rw [le_div'_iff_mul_le, mul_comm]
      simp only [qslMax]
      show _ ≤ `[qsl| [[P]] ⋆ [[Q]] ] s ⊔ `[qsl| [[P]] ⋆ [[R]] ] s
      rw [le_max_iff]
      right
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
  · intro s
    apply sup_le
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · apply ennreal_mul_le_mul le_rfl ?_
        simp only [qslMax]
        show _ ≤ Q _ ⊔ R _
        exact le_max_left _ _
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · apply ennreal_mul_le_mul le_rfl ?_
        simp only [qslMax]
        show _ ≤ Q _ ⊔ R _
        exact le_max_right _ _

theorem qslSepMul_qslAdd_subdistr (P Q R : StateRVInf Var) :
    `[qsl| [[P]] ⋆ ([[Q]] + [[R]])] ⊢ `[qsl| ([[P]] ⋆ [[Q]]) + ([[P]] ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [qslAdd]
  rw [ENNReal.left_distr]
  apply add_le_add
  · apply le_sSup
    use heap₁, heap₂
  · apply le_sSup
    use heap₁, heap₂


theorem qslSepMul_qslMul_of_iverson_subdistr (P : State Var → Prop) (Q R : StateRVInf Var) :
    `[qsl| ⁅P⁆ ⋆ ([[Q]] ⬝ [[R]]) ⊢ (⁅P⁆ ⋆ [[Q]]) ⬝ (⁅P⁆ ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [qslMul, qslIverson]
  rw [← iteOneZero_mul_self]
  apply le_trans
  · calc (iteOneZero _ * iteOneZero _) * (Q _ * R _)
    _ = (Q _ * R _) * (iteOneZero _ * iteOneZero _) := by rw [mul_comm]
    _ = (Q _ * R _) * iteOneZero _ * iteOneZero _ := by rw [← mul_assoc]
    _ = iteOneZero _ * (Q _ * R _) * iteOneZero _ := by rw [← mul_rotate]
    _ = iteOneZero _ * Q _ * R _ * iteOneZero _ := by rw [← mul_assoc]
    _ = iteOneZero _ * Q _ * (R _ * iteOneZero _) := by rw [mul_assoc]
    _ = iteOneZero _ * Q _ * (iteOneZero _ * R _) := by rw [mul_comm (R _) _]
    _ ≤ (iteOneZero _ * Q _) * (iteOneZero _ * R _) := le_rfl
  · apply ennreal_mul_le_mul
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rfl
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rfl

theorem qslSepMul_qslSup_distr (P : StateRVInf Var) (Q : α → StateRVInf Var) :
    `[qsl| [[P]] ⋆ S (a : α). [[Q a]]] = `[qsl| S (a : α). [[P]] ⋆ [[Q a]]] := by
  funext s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_comm, ← le_div'_iff_mul_le, qslSup_apply]
    apply iSup_le
    intro x
    rw [le_div'_iff_mul_le, mul_comm, qslSup_apply, le_iSup_iff]
    intro _ h
    apply le_trans ?_ (h x); clear h
    apply le_sSup
    use heap₁, heap₂
  · rw [qslSup_apply]
    apply iSup_le
    intro x
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply ennreal_mul_le_mul le_rfl
      rw [qslSup_apply, le_iSup_iff]
      intro _ h
      exact le_trans le_rfl (h x)

theorem qslSepMul_qslInf_subdistr (P : StateRVInf Var) (Q : α → StateRVInf Var) :
    `[qsl| [[P]] ⋆ I (a : α). [[Q a]] ⊢ I (a : α). [[P]] ⋆ [[Q a]]] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [qslInf_apply, le_iInf_iff]
  intro x
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union
  · apply ennreal_mul_le_mul le_rfl
    exact iInf_le _ _

theorem qslSepDiv_qslMax_supdistr (P Q R : StateRVInf Var) :
    `[qsl| ([[P]] -⋆ [[Q]]) ⊔ ([[P]] -⋆ [[R]])] ⊢ `[qsl| [[P]] -⋆ ([[Q]] ⊔ [[R]])] := by
  intro s
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  apply sup_le
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply div'_le_div' ?_ le_rfl
      simp only [qslMax]
      exact le_max_left _ _
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply div'_le_div' ?_ le_rfl
      simp only [qslMax]
      exact le_max_right _ _

theorem qslSepDiv_qslMin_distr (P Q R : StateRVInf Var) :
    `[qsl| ([[P]] -⋆ [[Q]]) ⊓ ([[P]] -⋆ [[R]])] = `[qsl| [[P]] -⋆ ([[Q]] ⊓ [[R]])] := by
  apply le_antisymm
  · intro s
    apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    rw [le_div'_iff_mul_le]
    apply le_inf
    · rw [← le_div'_iff_mul_le]
      simp only [qslMin]
      show `[qsl| [[P]] -⋆ [[Q]] ] s ⊓ `[qsl| [[P]] -⋆ [[R]] ] s ≤ _
      rw [min_le_iff]
      left
      apply sInf_le
      use heap, h_disjoint
    · rw [← le_div'_iff_mul_le]
      simp only [qslMin]
      show `[qsl| [[P]] -⋆ [[Q]] ] s ⊓ `[qsl| [[P]] -⋆ [[R]] ] s ≤ _
      rw [min_le_iff]
      right
      apply sInf_le
      use heap, h_disjoint
  · intro s
    apply le_inf
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      apply sInf_le_of_le
      · use heap, h_disjoint
      · apply div'_le_div' ?_ le_rfl
        simp only [qslMin]
        exact min_le_left _ _
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      apply sInf_le_of_le
      · use heap, h_disjoint
      · apply div'_le_div' ?_ le_rfl
        simp only [qslMin]
        exact min_le_right _ _

-- theorem qslSepDiv_qslAdd_supdistr (P Q R : StateRVInf Var) :
--     `[qsl| ([[P]] -⋆ [[Q]]) + ([[P]] -⋆ [[R]]) ⊢ [[P]] -⋆ ([[Q]] + [[R]])] := by
--   sorry

-- theorem qslSepdiv_weight_qslAdd_subdistr (P Q R : StateRVInf Var) :
--     `[fsl| <e> ⬝ ([[P]] -⋆ [[Q]]) + ~<e> ⬝ ([[P]] -⋆ [[R]])]
--     ⊢ `[fsl| [[P]] -⋆ (<e> ⬝ [[Q]] + ~<e> ⬝ [[R]])] := by
--   sorry

theorem qslSepDiv_qslSup_superdistr (P : StateRVInf Var) (Q : α → StateRVInf Var) :
    `[qsl| S (a : α). [[P]] -⋆ [[Q a]] ⊢  [[P]] -⋆ S (a : α). [[Q a]]] := by
  intro s
  rw [qslSup_apply]
  apply iSup_le
  intro x
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  rw [qslSup_apply]
  apply sInf_le_of_le
  · use heap, h_disjoint
  · apply div'_le_div' ?_ le_rfl
    rw [le_iSup_iff]
    intro _ h
    exact le_trans le_rfl (h x)

theorem qslSepDiv_qslInf_distr (P : StateRVInf Var) (Q : α → StateRVInf Var) :
    `[qsl| I (a : α). [[P]] -⋆ [[Q a]]] = `[qsl| [[P]] -⋆ I (a : α). [[Q a]]] := by
  funext s
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    rw [qslInf_apply, qslInf_apply, le_div'_iff_mul_le]
    apply le_iInf
    intro x
    rw [← le_div'_iff_mul_le, iInf_le_iff]
    rintro _ h
    apply le_trans (h x) ?_
    apply sInf_le
    use heap
  · rw [qslInf_apply]
    apply le_iInf
    intro x
    apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    apply sInf_le_of_le
    · use heap, h_disjoint
    · apply div'_le_div' ?_ le_rfl
      rw [qslInf_apply, iInf_le_iff]
      intro _ h
      exact le_trans (h x) le_rfl

end Separating

section Precise

theorem qslSepMul_qslMin_distr_of_precise (P Q R : StateRVInf Var) (h : precise P) :
    `[qsl| [[P]] ⋆ [[Q]] ⊓ [[R]]] = `[qsl| ([[P]] ⋆ [[Q]]) ⊓ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm (qslSepMul_qslMin_subdistr P Q R)
  intro s
  obtain ⟨heap₁, h_subset, h⟩ := h s
  obtain ⟨heap₂, h_disjoint, h_union⟩ := union_of_subset h_subset
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union.symm
  · simp only [qslMin, Inf.inf]
    show `[qsl| [[P]] ⋆ [[Q]] ] s ⊓ `[qsl| [[P]] ⋆ [[R]] ] s
      ≤ _ * (Q _ ⊓ R _)
    cases le_total (Q ⟨s.stack, heap₂⟩) (R ⟨s.stack, heap₂⟩)
    case inl h_le =>
      rw [min_eq_left h_le, min_le_iff]
      left
      apply sSup_le
      rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
      cases eq_or_ne heap₁ heap₁'
      case inl h_eq =>
        rw [h_eq] at h_union h_disjoint ⊢
        apply ennreal_mul_le_mul le_rfl ?_
        have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
        rw [this]
      case inr h_neq =>
        specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
        rw [h]
        simp only [zero_mul, zero_le]
    case inr h_le =>
      rw [min_eq_right h_le, min_le_iff]
      right
      apply sSup_le
      rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
      cases eq_or_ne heap₁ heap₁'
      case inl h_eq =>
        rw [h_eq] at h_union h_disjoint ⊢
        apply ennreal_mul_le_mul le_rfl ?_
        have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
        rw [this]
      case inr h_neq =>
        specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
        rw [h]
        simp only [zero_mul, zero_le]

end Precise

end QSL
