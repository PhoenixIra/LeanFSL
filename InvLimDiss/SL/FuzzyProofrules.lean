import InvLimDiss.SL.Fuzzy

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

namespace FSL

open unitInterval State

variable {Var : Type}

section Entailment

theorem entailment_iff_pi_le {P Q : StateRV Var} : P ⊢ Q ↔ P ≤ Q := by rfl

theorem entailment_iff_le {P Q : StateRV Var} : P ⊢ Q ↔ ∀ s, P s ≤ Q s := by
  unfold Entailment.entail instEntailmentStateRV
  simp only
  rw [Pi.le_def]

end Entailment

/-! We have here lemmas about separating multipication and division. -/
section Separating

theorem fslSepMul_mono {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
    `[fsl Var| [[P₁]] ⋆ [[Q₁]] ⊢ [[P₂]] ⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  apply le_sSup_iff.mpr
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro i h
  specialize h heap₁ heap₂ h_disjoint rfl rfl
  refine le_trans ?_ h; clear h
  apply unit_mul_le_mul
  · exact h_P ⟨s,heap₁⟩
  · exact h_Q ⟨s,heap₂⟩

theorem fslSepDiv_mono {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₂ ⊢ P₁) (h_Q : Q₁ ⊢ Q₂) :
    `[fsl| [[P₁]] -⋆ [[Q₁]] ⊢ [[P₂]] -⋆ [[Q₂]]] := by
  intro ⟨s,heap⟩
  apply le_sInf
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ h_disjoint rfl
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
  intro _ h
  specialize h heap₁ h_disjoint rfl
  apply le_trans h
  apply unit_div_le_div
  · exact h_Q ⟨s,heap ∪ heap₁⟩
  · exact h_P ⟨s,heap₁⟩

-- adjointness of sepcon and sepimp
theorem le_fslSepDiv_iff_fslSepMul_le (P₁ P₂ P₃ : StateRV Var) :
    `[fsl| [[P₁]] ⊢ [[P₂]] -⋆ [[P₃]]] ↔ `[fsl| [[P₁]] ⋆ [[P₂]] ⊢ [[P₃]]] := by
  apply Iff.intro
  case mp =>
    intro h ⟨s,heap⟩
    apply sSup_le
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₁ heap₂ h_disjoint rfl rfl
    cases eq_or_ne (P₂ ⟨s,heap₂⟩) 0 with
    | inl h_eq => rw [h_eq, mul_zero]; exact nonneg'
    | inr h_ne =>
      rw [← (unit_le_div_iff_mul_le)]
      specialize h ⟨s,heap₁⟩
      unfold fslSepDiv at h
      simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
      exact h (P₃ ⟨s,heap₁ ∪ heap₂⟩ / P₂ ⟨s,heap₂⟩) heap₂ h_disjoint rfl
  case mpr =>
    intro h ⟨s,heap₁⟩
    apply le_sInf
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₂ h_disjoint rfl
    rw [unit_le_div_iff_mul_le]
    specialize h ⟨s,heap₁ ∪ heap₂⟩
    unfold fslSepMul at h
    rw [sSup_le_iff] at h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h (P₁ ⟨s,heap₁⟩ * P₂ ⟨s,heap₂⟩) heap₁ heap₂ h_disjoint rfl rfl

-- modus ponens of sepimp and sepcon
theorem fslSepMul_fslSepDiv_entail (P₁ P₂ : StateRV Var) :
    `[fsl| ([[P₁]] -⋆ [[P₂]]) ⋆ [[P₁]] ⊢ [[P₂]]] := by
  rintro ⟨s,heap⟩
  apply sSup_le
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  rintro - heap₁ heap₂ h_disjoint rfl rfl
  cases eq_or_ne (P₁ ⟨s, heap₂⟩) 0
  case inl h_eq =>
    rw [h_eq, mul_zero]
    exact nonneg'
  case inr h_ne =>
    rw [← unit_le_div_iff_mul_le]
    apply sInf_le
    simp only [Set.mem_setOf_eq]
    exists heap₂

theorem fslSepDiv_eq_one (f₁ f₂ : StateRV Var) (s : State Var) :
    `[fsl| [[f₁]] -⋆ [[f₂]]] s = 1 ↔
    ∀ heap, disjoint s.heap heap →
      f₁ ⟨s.stack, heap⟩ ≤ f₂ ⟨s.stack, s.heap ∪ heap⟩ := by
  apply Iff.intro
  · intro h heap h_disjoint
    rw [← unit_div_eq_one_iff]
    apply le_antisymm le_one'
    rw [fslSepDiv] at h
    obtain h_inf := le_of_eq h.symm; clear h
    rw [le_sInf_iff] at h_inf
    specialize h_inf (f₂ ⟨s.stack, s.heap ∪ heap⟩ / f₁ ⟨s.stack, heap⟩)
    apply h_inf
    use heap
  · intro h
    conv at h => intro a b; rw [← unit_div_eq_one_iff]
    rw [fslSepDiv]
    apply le_antisymm le_one'
    apply le_sInf
    rintro i ⟨heap, h_disjoint, rfl⟩
    rw [h heap h_disjoint]

theorem fslSepMul_symm (f g : StateRV Var) : `[fsl| [[f]] ⋆ [[g]] ⊢ [[g]] ⋆ [[f]]] := by
  rw [Pi.le_def]
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  apply le_sSup
  use heap₂, heap₁
  rw [union_comm _ _ h_disjoint] at h_union
  rw [State.disjoint_comm] at h_disjoint
  use h_disjoint, h_union
  exact unit_mul_comm _ _

theorem fslSepMul_comm (f g : StateRV Var) : `[fsl| [[f]] ⋆ [[g]]] = `[fsl| [[g]] ⋆ [[f]]] :=
  le_antisymm (fslSepMul_symm f g) (fslSepMul_symm g f)

theorem fslSepMul_assoc_le (f₁ f₂ f₃ : StateRV Var) :
    `[fsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]] ⊢ ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂₃, h_disjoint₁, h_union₁, rfl⟩
  rw [mul_comm, ← unit_le_div_iff_mul_le]
  apply sSup_le
  rintro _ ⟨heap₂, heap₃, h_disjoint₂₃, h_union₂₃, rfl⟩
  rw [unit_le_div_iff_mul_le]
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
    refine mul_le_mul ?_ le_rfl nonneg' nonneg'
    apply le_sSup
    use heap₁, heap₂, h_disjoint₁.left

theorem fslSepMul_assoc (f₁ f₂ f₃ : StateRV Var) :
    `[fsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]]] = `[fsl| ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
  apply le_antisymm
  · exact fslSepMul_assoc_le f₁ f₂ f₃
  · rw [fslSepMul_comm _ f₃, fslSepMul_comm f₁ _]
    rw [fslSepMul_comm f₁ _, fslSepMul_comm f₂ f₃]
    exact fslSepMul_assoc_le f₃ f₂ f₁

theorem fslEmp_fslSepDiv_eq (f : StateRV Var) : `[fsl| emp -⋆ [[f]]] = f := by
  apply funext
  intro s
  apply le_antisymm
  · apply sInf_le
    use ∅, disjoint_emptyHeap'
    simp only [union_emptyHeap, fslEmp, iteOneZero_true, unit_div_one]
  · apply le_sInf
    rintro _ ⟨heap, _, rfl⟩
    simp only [fslEmp, iteOneZero_eq_iff]
    split
    case isTrue h => rw [h, union_emptyHeap, unit_div_one]
    case isFalse h => rw [unit_div_zero]; exact le_one'

theorem fslSepMul_fslEmp_eq (f : StateRV Var) : `[fsl| [[f]] ⋆ emp] = f := by
  apply funext
  intro s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
    simp only [fslEmp, iteOneZero_eq_iff, mul_ite, mul_one, mul_zero]
    split
    case isTrue h =>
      rw [h, union_emptyHeap] at h_union
      rw [h_union]
    case isFalse h => exact nonneg'
  · apply le_sSup
    use s.heap, ∅, disjoint_emptyHeap', union_emptyHeap'
    simp only [fslEmp, iteOneZero_true, mul_one]

theorem fslSepMul_fslFalse_eq (f : StateRV Var) : `[fsl| [[f]] ⋆ fFalse] = `[fsl| fFalse] := by
  apply funext
  intro s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨_, _, _, _, rfl⟩
    simp only [fslFalse, mul_zero, le_refl]
  · simp only [fslFalse, zero_le]

theorem fslSepMul_fslMin_subdistr (P Q R : StateRV Var) :
    `[fsl| [[P]] ⋆ ([[Q]] ⊓ [[R]])] ≤ `[fsl| ([[P]] ⋆ [[Q]]) ⊓ ([[P]] ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  apply le_inf
  · apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply unit_mul_le_mul le_rfl ?_
      simp only [fslMin, Inf.inf]
      rw [inf_le_iff]
      left
      rfl
  · apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply unit_mul_le_mul le_rfl ?_
      simp only [fslMin, Inf.inf]
      rw [inf_le_iff]
      right
      rfl

theorem fslSepMul_fslMax_distr (P Q R : StateRV Var) :
    `[fsl| [[P]] ⋆ ([[Q]] ⊔ [[R]])] = `[fsl| ([[P]] ⋆ [[Q]]) ⊔ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_comm, ← unit_le_div_iff_mul_le]
    apply sup_le
    · rw [unit_le_div_iff_mul_le, mul_comm]
      simp only [fslMax, Sup.sup, le_sup_iff]
      left
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
    · rw [unit_le_div_iff_mul_le, mul_comm]
      simp only [fslMax, Sup.sup, le_sup_iff]
      right
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
  · intro s
    apply sup_le
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · apply unit_mul_le_mul le_rfl ?_
        simp only [fslMax, Sup.sup, le_sup_left]
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · apply unit_mul_le_mul le_rfl ?_
        simp only [fslMax, Sup.sup, le_sup_right]

theorem fslSepDiv_fslMax_supdistr (P Q R : StateRV Var) :
    `[fsl| ([[P]] -⋆ [[Q]]) ⊔ ([[P]] -⋆ [[R]])] ⊢ `[fsl| [[P]] -⋆ ([[Q]] ⊔ [[R]])] := by
  intro s
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  apply sup_le
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply unit_div_le_div ?_ le_rfl
      simp only [fslMax, Sup.sup, le_sup_left]
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply unit_div_le_div ?_ le_rfl
      simp only [fslMax, Sup.sup, le_sup_right]

theorem fslSepDiv_fslMin_distr (P Q R : StateRV Var) :
    `[fsl| ([[P]] -⋆ [[Q]]) ⊓ ([[P]] -⋆ [[R]])] = `[fsl| [[P]] -⋆ ([[Q]] ⊓ [[R]])] := by
  apply le_antisymm
  · intro s
    apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    rw [unit_le_div_iff_mul_le]
    apply le_inf
    · rw [← unit_le_div_iff_mul_le]
      simp only [fslMin, Inf.inf, inf_le_iff]
      left
      apply sInf_le
      use heap, h_disjoint
    · rw [← unit_le_div_iff_mul_le]
      simp only [fslMin, Inf.inf, inf_le_iff]
      right
      apply sInf_le
      use heap, h_disjoint
  · intro s
    apply le_inf
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      apply sInf_le_of_le
      · use heap, h_disjoint
      · apply unit_div_le_div ?_ le_rfl
        simp only [fslMin, Inf.inf, inf_le_left]
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      apply sInf_le_of_le
      · use heap, h_disjoint
      · apply unit_div_le_div ?_ le_rfl
        simp only [fslMin, Inf.inf, inf_le_right]

end Separating

section Precise

theorem fslSepMul_fslMin_distr_of_precise (P Q R : StateRV Var) (h : precise P) :
    `[fsl| [[P]] ⋆ ([[Q]] ⊓ [[R]])] = `[fsl| ([[P]] ⋆ [[Q]]) ⊓ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm (fslSepMul_fslMin_subdistr P Q R)
  intro s
  obtain ⟨heap₁, h_subset, h⟩ := h s
  obtain ⟨heap₂, h_disjoint, h_union⟩ := union_of_subset h_subset
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union.symm
  · simp only [fslMin, Inf.inf]
    cases le_total (Q ⟨s.stack, heap₂⟩) (R ⟨s.stack, heap₂⟩)
    case inl h_le =>
      rw [inf_of_le_left h_le, inf_le_iff]
      left
      apply sSup_le
      rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
      cases eq_or_ne heap₁ heap₁'
      case inl h_eq =>
        rw [h_eq] at h_union h_disjoint ⊢
        apply unit_mul_le_mul le_rfl ?_
        have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
        rw [this]
      case inr h_neq =>
        specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
        rw [h]
        simp only [zero_mul, zero_le]
    case inr h_le =>
      rw [inf_of_le_right h_le, inf_le_iff]
      right
      apply sSup_le
      rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
      cases eq_or_ne heap₁ heap₁'
      case inl h_eq =>
        rw [h_eq] at h_union h_disjoint ⊢
        apply unit_mul_le_mul le_rfl ?_
        have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
        rw [this]
      case inr h_neq =>
        specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
        rw [h]
        simp only [zero_mul, zero_le]

end Precise

/-! This features elimination rules for quantifiers in fsl. -/
section Quantifiers

theorem fslSup_apply (P : α → StateRV Var) (s : State Var) :
    `[fsl| S x. [[P x]]] s = ⨆ x, P x s := by
  rw [fslSup, iSup_apply]

theorem fslInf_apply (P : α → StateRV Var) (s : State Var) :
    `[fsl| I x. [[P x]]] s = ⨅ x, P x s := by
  rw [fslInf, iInf_apply]

end Quantifiers

section PointsTo

open State HeapValue Syntax

theorem fslMax_entailment_iff (P Q R : StateRV Var) :
    `[fsl| [[P]] ⊔ [[Q]] ⊢ [[R]]] ↔ P ⊢ R ∧ Q ⊢ R := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [fslMax, Sup.sup, sup_le_iff] at h
      exact h.left
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [fslMax, Sup.sup, sup_le_iff] at h
      exact h.right
  · rintro ⟨h_P, h_Q⟩
    intro s
    simp only [fslMax, Sup.sup, sup_le_iff]
    exact ⟨h_P s, h_Q s⟩

theorem fslBigSepMul_of_fslPointsTo_of_bigSingleton_eq_one {l : ℕ+} {stack : Stack Var}:
    `[fsl| [⋆] i ∈ { ... n}. (l+i:ℚ) ↦ (0:ℚ)] ⟨stack, bigSingleton l n 0⟩ = 1 := by
  induction n with
  | zero =>
    simp only [fslBigSepMul, fslEmp, iteOneZero_eq_one_def, bigSingleton_of_zero]
  | succ n ih =>
    simp only [fslBigSepMul, bigSingleton, Pi.zero_apply]
    apply le_antisymm le_one'
    apply le_sSup
    use (singleton ⟨l+n,PNat.add_right_nat⟩ 0), (bigSingleton l n 0)
    use disjoint_singleton_bigSingleton le_rfl
    apply And.intro
    · simp only
      rw [union_comm, ← union_singleton_bigSingle]
      · simp only [Pi.zero_apply]
      · exact disjoint_singleton_bigSingleton le_rfl
    simp only [fslPointsTo]
    rw [iteOneZero_pos]
    pick_goal 2
    · use ⟨l+n,PNat.add_right_nat⟩
      simp only [PNat.mk_coe, Nat.cast_add, and_self]
    · simp only [ih, mul_one]

end PointsTo

end FSL
