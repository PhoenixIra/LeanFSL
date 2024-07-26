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
  * Eliminating theorems about quantifiers
-/

namespace QSL

open unitInterval State

variable {Var : Type}

section Entailment

theorem entailment_iff_le {P Q : StateRV Var} : P ⊢ Q ↔ ∀ s, P s ≤ Q s := by
  unfold Entailment.entail instEntailmentStateRV
  simp only
  rw [Pi.le_def]

end Entailment

/-! We have here lemmas about separating multipication and division. -/
section Separating

theorem monotone_qslSepMul {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₁ ⊢ P₂) (h_Q : Q₁ ⊢ Q₂) :
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
  apply unit_mul_le_mul
  · exact h_P ⟨s,heap₁⟩
  · exact h_Q ⟨s,heap₂⟩

theorem monotone_qslSepDiv {P₁ P₂ Q₁ Q₂ : StateRV Var} (h_P : P₂ ⊢ P₁) (h_Q : Q₁ ⊢ Q₂) :
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
  apply unit_div_le_div
  · exact h_Q ⟨s,heap ∪ heap₁⟩
  · exact h_P ⟨s,heap₁⟩

-- adjointness of sepcon and sepimp
theorem le_qslSepDiv_iff_qslSepMul_le (P₁ P₂ P₃ : StateRV Var) :
    `[qsl| [[P₁]] ⊢ [[P₂]] -⋆ [[P₃]]] ↔ `[qsl| [[P₁]] ⋆ [[P₂]] ⊢ [[P₃]]] := by
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
      unfold qslSepDiv at h
      simp only [le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp] at h
      exact h (P₃ ⟨s,heap₁ ∪ heap₂⟩ / P₂ ⟨s,heap₂⟩) heap₂ h_disjoint rfl
  case mpr =>
    intro h ⟨s,heap₁⟩
    apply le_sInf
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro - heap₂ h_disjoint rfl
    rw [unit_le_div_iff_mul_le]
    specialize h ⟨s,heap₁ ∪ heap₂⟩
    unfold qslSepMul at h
    rw [sSup_le_iff] at h
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp] at h
    exact h (P₁ ⟨s,heap₁⟩ * P₂ ⟨s,heap₂⟩) heap₁ heap₂ h_disjoint rfl rfl

-- modus ponens of sepimp and sepcon
theorem qslSepMul_qslSepDiv_entail (P₁ P₂ : StateRV Var) :
    `[qsl| ([[P₁]] -⋆ [[P₂]]) ⋆ [[P₁]] ⊢ [[P₂]]] := by
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

theorem qslSepDiv_eq_one (f₁ f₂ : StateRV Var) (s : State Var) :
    `[qsl| [[f₁]] -⋆ [[f₂]]] s = 1 ↔
    ∀ heap, disjoint s.heap heap →
      f₁ ⟨s.stack, heap⟩ ≤ f₂ ⟨s.stack, s.heap ∪ heap⟩ := by
  apply Iff.intro
  · intro h heap h_disjoint
    rw [← unit_div_eq_one_iff]
    apply le_antisymm le_one'
    rw [qslSepDiv] at h
    obtain h_inf := le_of_eq h.symm; clear h
    rw [le_sInf_iff] at h_inf
    specialize h_inf (f₂ ⟨s.stack, s.heap ∪ heap⟩ / f₁ ⟨s.stack, heap⟩)
    apply h_inf
    use heap
  · intro h
    conv at h => intro a b; rw [← unit_div_eq_one_iff]
    rw [qslSepDiv]
    apply le_antisymm le_one'
    apply le_sInf
    rintro i ⟨heap, h_disjoint, rfl⟩
    rw [h heap h_disjoint]

theorem qslSepMul_symm (f g : StateRV Var) : `[qsl| [[f]] ⋆ [[g]] ⊢ [[g]] ⋆ [[f]]] := by
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

theorem qslSepMul_comm (f g : StateRV Var) : `[qsl| [[f]] ⋆ [[g]]] = `[qsl| [[g]] ⋆ [[f]]] :=
  le_antisymm (qslSepMul_symm f g) (qslSepMul_symm g f)

theorem qslSepMul_assoc_le (f₁ f₂ f₃ : StateRV Var) :
    `[qsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]] ⊢ ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
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

theorem qslSepMul_assoc (f₁ f₂ f₃ : StateRV Var) :
    `[qsl| [[f₁]] ⋆ [[f₂]] ⋆ [[f₃]]] = `[qsl| ([[f₁]] ⋆ [[f₂]]) ⋆ [[f₃]]] := by
  apply le_antisymm
  · exact qslSepMul_assoc_le f₁ f₂ f₃
  · rw [qslSepMul_comm _ f₃, qslSepMul_comm f₁ _]
    rw [qslSepMul_comm f₁ _, qslSepMul_comm f₂ f₃]
    exact qslSepMul_assoc_le f₃ f₂ f₁

theorem qslEmp_qslSepDiv_eq (f : StateRV Var) : `[qsl| emp -⋆ [[f]]] = f := by
  apply funext
  intro s
  apply le_antisymm
  · apply sInf_le
    use ∅, disjoint_emptyHeap'
    simp only [union_emptyHeap, qslEmp, iteOneZero_true, unit_div_one]
  · apply le_sInf
    rintro _ ⟨heap, _, rfl⟩
    simp only [qslEmp, iteOneZero_eq_iff]
    split
    case isTrue h => rw [h, union_emptyHeap, unit_div_one]
    case isFalse h => rw [unit_div_zero]; exact le_one'

theorem qslSepMul_qslEmp_eq (f : StateRV Var) : `[qsl| [[f]] ⋆ emp] = f := by
  apply funext
  intro s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
    simp only [qslEmp, iteOneZero_eq_iff, mul_ite, mul_one, mul_zero]
    split
    case isTrue h =>
      rw [h, union_emptyHeap] at h_union
      rw [h_union]
    case isFalse h => exact nonneg'
  · apply le_sSup
    use s.heap, ∅, disjoint_emptyHeap', union_emptyHeap'
    simp only [qslEmp, iteOneZero_true, mul_one]

theorem qslSepMul_qslFalse_eq (f : StateRV Var) : `[qsl| [[f]] ⋆ qFalse] = `[qsl| qFalse] := by
  apply funext
  intro s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨_, _, _, _, rfl⟩
    simp only [qslFalse, mul_zero, le_refl]
  · simp only [qslFalse, zero_le]

end Separating

/-! This features elimination rules for quantifiers in qsl. -/
section Quantifiers

theorem qslSup_apply (P : α → StateRV Var) (s : State Var) :
    `[qsl| S x. [[P x]]] s = sSup {y | ∃ x, P x s = y} := by
  rw [qslSup, sSup_apply, iSup, Set.range]
  simp only [Subtype.exists, exists_prop]
  apply le_antisymm
  · apply sSup_le_sSup
    rintro i ⟨P', ⟨⟨x, hx⟩, hP'⟩⟩
    use x
    rw [hx, hP']
  · apply sSup_le_sSup
    rintro i ⟨x, hx⟩
    use (P x)
    refine And.intro ?_ hx
    use x

theorem qslInf_apply (P : α → StateRV Var) (s : State Var) :
    `[qsl| I x. [[P x]]] s = sInf {y | ∃ x, P x s = y} := by
  rw [qslInf, sInf_apply, iInf, Set.range]
  simp only [Subtype.exists, exists_prop]
  apply le_antisymm
  · apply sInf_le_sInf
    intro i ⟨x, hx⟩
    use (P x)
    refine And.intro ?_ hx
    use x
  · apply sInf_le_sInf
    intro i ⟨P', ⟨⟨x, hx⟩, hP'⟩⟩
    use x
    rw [hx, hP']

end Quantifiers

section PointsTo

open State HeapValue Syntax


theorem qslSup_qslPointsTo_qslSepMul_iff (e : ValueExp Var) (s : State Var) (P : ℚ → StateRV Var) :
    ∃ (q : ℚ), `[qsl| S (x : ℚ). e ↦ x ⋆ [[P x]]] s
             = `[qsl| e ↦ q ⋆ [[P q]]] s := by
  by_cases ∃ l : ℕ+, (e s.stack) = l ∧ s.heap l ≠ undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    rw [undef_iff_exists_val] at h_alloc
    obtain ⟨q, h_q⟩ := h_alloc
    use q
    apply le_antisymm
    · apply sSup_le
      simp only [Set.mem_range, Subtype.exists, exists_prop, qslPointsTo, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂]
      rintro _ ⟨q', rfl⟩
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · simp only [qslPointsTo, iteOneZero_eq_iff]
        split_ifs
        case pos h' h =>
          simp only [one_mul]
          obtain ⟨l, h_l, h_heap⟩ := h
          obtain ⟨l', h_l', h_heap'⟩ := h'
          simp only [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
          rw [h_l', h_heap, singleton_eq_singleton_iff_eq] at h_heap'
          rw [h_heap']
        case neg h' h =>
          exfalso
          obtain ⟨l' , h_l', h_heap⟩ := h'
          simp only [h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
          obtain rfl := h_l'
          have h_heap₁ := congrFun h_heap l'
          simp only [State.singleton, ↓reduceIte] at h_heap₁
          have h_q' := congrFun h_union l'
          simp only [union_eq_of_left h_heap₁, h_q, val.injEq] at h_q'
          simp only [not_exists, not_and] at h
          apply h l' h_l.symm
          rw [h_heap, h_q']
        case pos =>
          simp only [zero_mul, one_mul, zero_le]
        case neg =>
          simp only [zero_mul, le_refl]
    · apply le_sSup
      simp only [Set.mem_range, Subtype.exists, exists_prop]
      use (`[qsl| e ↦ q ⋆ [[P q]]])
      apply And.intro
      · use q
      · rfl
  case neg h =>
    simp only [ne_eq, not_exists, not_and, not_not] at h
    use (e s.stack)
    apply le_antisymm
    · apply sSup_le
      simp only [Set.mem_range, Subtype.exists, exists_prop, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro _ ⟨q, rfl⟩
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
      simp only [qslPointsTo, iteOneZero_eq_iff]
      split
      case isTrue h' =>
        exfalso
        obtain ⟨l, h_l, h_heap⟩ := h'
        rw [Eq.comm, singleton_eq_iff] at h_heap
        obtain ⟨h_heap₁_def, _⟩ := h_heap
        have := h l h_l.symm
        rw [← h_union, union_undef_iff_undef, h_heap₁_def] at this
        simp only [false_and] at this
      case isFalse h' =>
        simp only [zero_mul, zero_le]
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
      simp only [qslPointsTo, iteOneZero_eq_iff, ite_mul, one_mul, zero_mul]
      rw [if_neg]
      · simp only [zero_le]
      · simp only [not_exists, not_and]
        intro l h_l h_heap₁
        have h_heap_l := congrFun h_union l
        rw [h l h_l.symm, union_undef_iff_undef] at h_heap_l
        rw [Eq.comm, singleton_eq_iff, h_heap_l.left] at h_heap₁
        simp only [ne_eq, false_and] at h_heap₁

theorem qslSup_qslPointsTo_iff (e : ValueExp Var) (s : State Var) :
    ∃ (q : ℚ), `[qsl| S (x : ℚ). e ↦ x] s = `[qsl| e ↦ q] s := by
  obtain ⟨q, h⟩ := qslSup_qslPointsTo_qslSepMul_iff e s (fun _ => `[qsl| emp])
  use q
  rw [← qslSepMul_qslEmp_eq `[qsl| e ↦ q], ← h]
  conv => right; left; intro x; rw [qslSepMul_qslEmp_eq]

theorem qslMax_entailment_iff (P Q R : StateRV Var) :
    `[qsl| [[P]] ⊔ [[Q]] ⊢ [[R]]] ↔ P ⊢ R ∧ Q ⊢ R := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [qslMax, Sup.sup, sup_le_iff] at h
      exact h.left
    · intro s
      rw [Pi.le_def] at h
      specialize h s
      simp only [qslMax, Sup.sup, sup_le_iff] at h
      exact h.right
  · rintro ⟨h_P, h_Q⟩
    intro s
    simp only [qslMax, Sup.sup, sup_le_iff]
    exact ⟨h_P s, h_Q s⟩







end PointsTo

end QSL
