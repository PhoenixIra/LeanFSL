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

section Atoms

open Syntax

theorem fslEquals_rfl (P : ValueExp Var) : `[fsl| P === P] = `[fsl| fTrue] := by
  funext s
  unfold fslEquals fslTrue
  simp only [iteOneZero_true]

theorem le_fslTrue (P : StateRV Var) : P ⊢ `[fsl| fTrue] := by
  intro s
  unfold fslTrue
  exact le_one'

theorem fslFalse_le (P : StateRV Var) : `[fsl| fFalse] ⊢ P := by
  intro s
  unfold fslFalse
  exact nonneg'

end Atoms

/-! Proofrules for maxima and minima-/
section MaxMin

theorem fslMax_comm (P Q : StateRV Var) :
    `[fsl| [[P]] ⊔ [[Q]]] = `[fsl| [[Q]] ⊔ [[P]]] := by
  simp only [fslMax]
  exact sup_comm P Q

theorem fslMax_assoc (P Q R : StateRV Var) :
    `[fsl| ([[P]] ⊔ [[Q]]) ⊔ [[R]]] = `[fsl| [[P]] ⊔ [[Q]] ⊔ [[R]]] := by
  simp only [fslMax]
  exact sup_assoc P Q R

theorem fslMin_comm (P Q : StateRV Var) :
    `[fsl| [[P]] ⊓ [[Q]]] = `[fsl| [[Q]] ⊓ [[P]]] := by
  simp only [fslMin]
  exact inf_comm P Q

theorem fslMin_assoc (P Q R : StateRV Var) :
    `[fsl| ([[P]] ⊓ [[Q]]) ⊓ [[R]]] = `[fsl| [[P]] ⊓ [[Q]] ⊓ [[R]]] := by
  simp only [fslMin]
  exact inf_assoc P Q R

theorem fslMax_le_iff (P Q R : StateRV Var) :
    `[fsl| [[P]] ⊔ [[Q]] ⊢ [[R]]] ↔ P ⊢ R ∧ Q ⊢ R := by
  unfold fslMax
  exact sup_le_iff

theorem le_fslMax (P Q R : StateRV Var) (h : P ⊢ Q ∨ P ⊢ R) :
    `[fsl| [[P]] ⊢ [[Q]] ⊔ [[R]]] := by
  unfold fslMax
  intro s
  rw [Pi.sup_apply, le_sup_iff]
  cases h
  case inl h => left; exact h s
  case inr h => right; exact h s

theorem fslMin_le (P Q R : StateRV Var) (h : P ⊢ R ∨ Q ⊢ R) :
    `[fsl| [[P]] ⊓ [[Q]] ⊢ [[R]]] := by
  unfold fslMin
  intro s
  rw [Pi.inf_apply, inf_le_iff]
  cases h
  case inl h => left; exact h s
  case inr h => right; exact h s

theorem le_fslMin_iff (P Q R : StateRV Var) :
    `[fsl| [[P]] ⊢ [[Q]] ⊓ [[R]]] ↔ P ⊢ Q ∧ P ⊢ R := by
  unfold fslMin
  exact le_inf_iff

theorem fslTrue_fslMax (P : StateRV Var) :
    `[fsl| fTrue ⊔ [[P]]] = `[fsl| fTrue] := by
  funext s
  unfold fslMax fslTrue
  rw [Pi.sup_apply, sup_eq_left]
  exact le_one'

theorem fslMax_fslTrue (P : StateRV Var) :
    `[fsl| [[P]] ⊔ fTrue] = `[fsl| fTrue] := by
  rw [fslMax_comm]
  exact fslTrue_fslMax _

theorem fslTrue_fslMin (P : StateRV Var) :
    `[fsl| fTrue ⊓ [[P]]] = P := by
  funext s
  unfold fslMin fslTrue
  rw [Pi.inf_apply, inf_eq_right]
  exact le_one'

theorem fslMin_fslTrue (P : StateRV Var) :
    `[fsl| [[P]] ⊓ fTrue] = P := by
  rw [fslMin_comm]
  exact fslTrue_fslMin _

theorem fslMax_self (P : StateRV Var) :
    `[fsl| [[P]] ⊔ [[P]]] = P := by
  apply le_antisymm
  · rw [fslMax_le_iff]
    exact And.intro le_rfl le_rfl
  · apply le_fslMax
    left
    exact le_rfl

theorem fslMin_self (P : StateRV Var) :
    `[fsl| [[P]] ⊓ [[P]]] = P := by
  apply le_antisymm
  · apply fslMin_le
    left
    exact le_rfl
  · rw [le_fslMin_iff]
    exact And.intro le_rfl le_rfl

theorem fslMin_fslMax_right (P Q R : StateRV Var) :
    `[fsl| ([[P]] ⊔ [[Q]]) ⊓ [[R]]] = `[fsl| ([[P]] ⊓ [[R]]) ⊔ ([[Q]] ⊓ [[R]])] := by
  funext s
  simp only [fslMin, fslMax]
  rw [Pi.sup_apply, Pi.inf_apply, Pi.sup_apply, Pi.inf_apply, Pi.inf_apply]
  exact inf_sup_right (P s) (Q s) (R s)

theorem fslMax_fslMin_right (P Q R : StateRV Var) :
    `[fsl| ([[P]] ⊓ [[Q]]) ⊔ [[R]]] = `[fsl| ([[P]] ⊔ [[R]]) ⊓ ([[Q]] ⊔ [[R]])] := by
  funext s
  simp only [fslMin, fslMax]
  rw [Pi.sup_apply, Pi.inf_apply, Pi.inf_apply, Pi.sup_apply, Pi.sup_apply]
  exact sup_inf_right (P s) (Q s) (R s)

theorem fslMin_le_fslMin {P₁ P₂ Q₁ Q₂ : StateRV Var} (h₁ : P₁ ⊢ Q₁) (h₂ : P₂ ⊢ Q₂) :
    `[fsl| [[P₁]] ⊓ [[P₂]]] ⊢ `[fsl| [[Q₁]] ⊓ [[Q₂]]] := by
  rw [entailment_iff_pi_le, le_fslMin_iff]
  apply And.intro
  · apply fslMin_le
    exact Or.inl h₁
  · apply fslMin_le
    exact Or.inr h₂

theorem fslMax_le_fslMax {P₁ P₂ Q₁ Q₂ : StateRV Var} (h₁ : P₁ ⊢ Q₁) (h₂ : P₂ ⊢ Q₂) :
    `[fsl| [[P₁]] ⊔ [[P₂]]] ⊢ `[fsl| [[Q₁]] ⊔ [[Q₂]]] := by
  rw [entailment_iff_pi_le, fslMax_le_iff]
  apply And.intro
  · apply le_fslMax
    exact Or.inl h₁
  · apply le_fslMax
    exact Or.inr h₂

end MaxMin

section Arithmetic

theorem fslAdd_mono {P₁ P₂ Q₁ Q₂ : StateRV Var} :
    P₁ ⊢ P₂ → Q₁ ⊢ Q₂ → `[fsl| [[P₁]] + [[Q₁]] ⊢ [[P₂]] + [[Q₂]]] := by
  intro h_P h_Q s
  exact truncatedAdd_le_truncatedAdd _ _ _ _ (h_P s) (h_Q s)

theorem fslMul_mono {P₁ P₂ Q₁ Q₂ : StateRV Var} :
    P₁ ⊢ P₂ → Q₁ ⊢ Q₂ → `[fsl| [[P₁]] ⬝ [[Q₁]] ⊢ [[P₂]] ⬝ [[Q₂]]] := by
  intro h_P h_Q s
  exact unit_mul_le_mul (h_P s) (h_Q s)

theorem fslAdd_fslFalse (P : StateRV Var) :
    `[fsl| [[P]] + fFalse] = P := by
  funext s
  simp only [fslAdd, fslFalse, add_zero]

theorem fslMul_fslFalse (P : StateRV Var) :
    `[fsl| [[P]] ⬝ fFalse] = fslFalse := by
  funext s
  simp only [fslMul, fslFalse, mul_zero]

open Syntax in
theorem fslReal_fslMul_fslTrue (r : ProbExp Var) : `[fsl| <r> ⬝ fTrue] = `[fsl| <r>] := by
  funext s
  simp only [fslMul, fslTrue, mul_one]

theorem fslMul_comm {P Q : StateRV Var} : `[fsl| [[P]] ⬝ [[Q]]] = `[fsl| [[Q]] ⬝ [[P]]] := by
  funext s
  simp only [fslMul, mul_comm]

theorem fslAdd_comm {P Q : StateRV Var} : `[fsl| [[P]] + [[Q]]] = `[fsl| [[Q]] + [[P]]] := by
  funext s
  simp only [fslAdd, add_comm]

theorem fslMul_assoc {P Q R : StateRV Var} :
    `[fsl| [[P]] ⬝ [[Q]] ⬝ [[R]]] = `[fsl| ([[P]] ⬝ [[Q]]) ⬝ [[R]]] := by
  funext s
  simp only [fslMul, mul_assoc]

theorem fslAdd_assoc {P Q R : StateRV Var} :
    `[fsl| [[P]] + [[Q]] + [[R]]] = `[fsl| ([[P]] + [[Q]]) + [[R]]] := by
  funext s
  simp only [fslAdd, add_assoc]

theorem fslAdd_weighted_self {P : StateRV Var} :
    `[fsl| <e> ⬝ [[P]] + ~<e> ⬝ [[P]]] = P := by
  funext s
  simp only [fslAdd, fslMul, fslReal, fslNot]
  exact truncatedAdd_sym_mul_eq _ _

end Arithmetic

/-! This features elimination rules for quantifiers in fsl. -/
section Quantifiers

theorem fslSup_apply (P : α → StateRV Var) (s : State Var) :
    `[fsl| S x. [[P x]]] s = ⨆ x, P x s := by
  rw [fslSup, iSup_apply]

theorem fslInf_apply (P : α → StateRV Var) (s : State Var) :
    `[fsl| I x. [[P x]]] s = ⨅ x, P x s := by
  rw [fslInf, iInf_apply]

theorem fslSup_le (P : α → StateRV Var) (Q : StateRV Var)
    (h : ∀ x : α, P x ⊢ Q) :
    `[fsl| S x. [[P x]] ⊢ [[Q]]] := by
  intro s
  rw [fslSup_apply]
  apply iSup_le
  intro x
  exact h x s

theorem le_fslSup (P : α → StateRV Var) (Q : StateRV Var)
    (x : α) (h : Q ⊢ P x) :
    `[fsl| [[Q]] ⊢ S x. [[P x]]] := by
  intro s
  rw [fslSup_apply]
  apply le_trans (h s)
  apply le_iSup _ x

theorem fslInf_le (P : α → StateRV Var) (Q : StateRV Var)
    (x : α) (h : P x ⊢ Q) :
    `[fsl| I x. [[P x]] ⊢ [[Q]]] := by
  intro s
  rw [fslInf_apply]
  apply le_trans (iInf_le _ x)
  exact h s

theorem le_fslInf (P : α → StateRV Var) (Q : StateRV Var)
    (h : ∀ x : α, Q ⊢ P x) :
    `[fsl| [[Q]] ⊢ I x. [[P x]]] := by
  intro s
  rw [fslInf_apply]
  apply le_iInf
  intro x
  exact h x s


end Quantifiers

section Iverson

open SL

theorem fslIverson_fslMin_eq_fslIverson_fslMul {Q : StateProp Var} {P : StateRV Var} :
    `[fsl| ⁅Q⁆ ⊓ [[P]]] = `[fsl| ⁅Q⁆ ⬝ [[P]]] := by
  funext s
  simp only [fslMin, fslMul]
  rw [Pi.inf_apply]
  simp only [fslIverson, inf_le_iff]
  by_cases (Q s)
  case pos h =>
    rw [iteOneZero_pos h]
    simp only [one_mul, inf_eq_right]
    exact le_one'
  case neg h =>
    rw [iteOneZero_neg h]
    simp only [zero_le, inf_of_le_left, zero_mul]

end Iverson

section PointsTo

open State HeapValue Syntax

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
    simp only [fslEmp, iteOneZero_eq_ite]
    split
    case isTrue h => rw [h, union_emptyHeap, unit_div_one]
    case isFalse h => rw [unit_div_zero]; exact le_one'

theorem fslSepMul_fslEmp_eq (f : StateRV Var) : `[fsl| [[f]] ⋆ emp] = f := by
  apply funext
  intro s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
    simp only [fslEmp, iteOneZero_eq_ite, mul_ite, mul_one, mul_zero]
    split
    case isTrue h =>
      rw [h, union_emptyHeap] at h_union
      rw [h_union]
    case isFalse h => exact nonneg'
  · apply le_sSup
    use s.heap, ∅, disjoint_emptyHeap', union_emptyHeap'
    simp only [fslEmp, iteOneZero_true, mul_one]

open Syntax
theorem fslReal_fslSepMul_fslTrue (r : ProbExp Var) : `[fsl| <r> ⋆ fTrue] = `[fsl| <r>] := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨h₁, h₂, h_disjoint, h_union, rfl⟩
    simp only [fslReal, fslTrue, mul_one, le_refl]
  · intro s
    apply le_sSup
    use s.heap, ∅, disjoint_emptyHeap _, union_emptyHeap _
    simp only [fslReal, fslTrue, mul_one]

theorem fslTrue_fslSepMul_fslTrue : `[fsl Var| fTrue ⋆ fTrue] = `[fsl Var| fTrue] := by
  funext s
  simp only [fslSepMul, fslTrue, mul_one]
  apply le_antisymm le_one'
  apply le_sSup
  use s.heap, ∅, disjoint_emptyHeap _, union_emptyHeap _

theorem fslTrue_fslSepMul_fslEquals : `[fsl| fTrue ⋆ e === e'] = `[fsl| e === e'] := by
  funext s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    simp only [fslTrue, fslEquals, one_mul, le_refl]
  · apply le_sSup_of_le
    use s.heap, ∅, disjoint_emptyHeap', union_emptyHeap'
    simp only [fslEquals, fslTrue, one_mul, le_refl]

theorem fslReal_fslMul_fslSepMul_assoc (r : ProbExp Var) (f g : StateRV Var) :
    `[fsl|<r> ⬝ [[f]] ⋆ [[g]]] = `[fsl| (<r> ⬝ [[f]]) ⋆ [[g]]] := by
  funext s
  simp only [fslMul, fslReal, fslSepMul]
  apply le_antisymm
  · rw [mul_comm, ← unit_le_div_iff_mul_le]
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [unit_le_div_iff_mul_le]
    apply le_sSup
    use heap₁, heap₂, h_disjoint, h_union
    rw [mul_comm, mul_assoc]
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_assoc]
    apply unit_mul_le_mul le_rfl
    apply le_sSup
    use heap₁, heap₂

theorem fslEmp_fslMul_fslSepMul_distr (f g : StateRV Var) :
    `[fsl| emp ⬝ ([[f]] ⋆ [[g]])] = `[fsl| (emp ⬝ [[f]]) ⋆ (emp ⬝ [[g]])] := by
  funext s
  apply le_antisymm
  · simp only [fslMul, fslEmp, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
    split
    case isTrue h_emp =>
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rw [← h_union, union_eq_emptyHeap_iff] at h_emp
      apply congrArg₂
      · simp only [fslMul, fslEmp, iteOneZero_pos h_emp.left, one_mul]
      · simp only [fslMul, fslEmp, iteOneZero_pos h_emp.right, one_mul]
    case isFalse => exact nonneg'
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    conv => right; rw [fslMul, fslEmp]
    simp only [iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
    split
    case isTrue h_emp =>
      rw [← h_union, union_eq_emptyHeap_iff] at h_emp
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      apply congrArg₂
      · simp only [fslMul, fslEmp, iteOneZero_pos h_emp.left, one_mul]
      · simp only [fslMul, fslEmp, iteOneZero_pos h_emp.right, one_mul]
    case isFalse h_n_emp =>
      simp only [fslMul, fslEmp, nonpos_iff_eq_zero, mul_eq_zero, iteOneZero_eq_zero_def]
      simp only [← h_union, union_eq_emptyHeap_iff, not_and_or] at h_n_emp
      cases h_n_emp
      case inl h₁ => left; left; exact h₁
      case inr h₂ => right; left; exact h₂


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
      exact min_le_left _ _
  · apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply unit_mul_le_mul le_rfl ?_
      simp only [fslMin, Inf.inf]
      exact min_le_right _ _

theorem fslSepMul_fslMax_distr (P Q R : StateRV Var) :
    `[fsl| [[P]] ⋆ ([[Q]] ⊔ [[R]])] = `[fsl| ([[P]] ⋆ [[Q]]) ⊔ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_comm, ← unit_le_div_iff_mul_le]
    apply sup_le
    · rw [unit_le_div_iff_mul_le, mul_comm]
      simp only [fslMax]
      show _ ≤ ( `[fsl| [[P]] ⋆ [[Q]]] s) ⊔ (`[fsl| [[P]] ⋆ [[R]]] s)
      rw [le_max_iff]
      left
      apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
    · rw [unit_le_div_iff_mul_le, mul_comm]
      simp only [fslMax]
      show _ ≤ `[fsl| [[P]] ⋆ [[Q]] ] s ⊔ `[fsl| [[P]] ⋆ [[R]] ] s
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
      · apply unit_mul_le_mul le_rfl ?_
        simp only [fslMax]
        show _ ≤ Q ⟨s.stack, heap₂⟩ ⊔ R ⟨s.stack, heap₂⟩
        rw [le_max_iff]
        left
        rfl
    · apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · apply unit_mul_le_mul le_rfl ?_
        simp only [fslMax]
        show _ ≤ Q ⟨s.stack, heap₂⟩ ⊔ R ⟨s.stack, heap₂⟩
        rw [le_max_iff]
        right
        rfl

theorem fslSepMul_fslAdd_subdistr (P Q R : StateRV Var) :
    `[fsl| [[P]] ⋆ ([[Q]] + [[R]])] ⊢ `[fsl| ([[P]] ⋆ [[Q]]) + ([[P]] ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [fslAdd]
  apply le_trans (left_subdistr_of_unit _ _ _)
  apply truncatedAdd_le_truncatedAdd
  · apply le_sSup
    use heap₁, heap₂
  · apply le_sSup
    use heap₁, heap₂

theorem fslSepMul_weight_fslAdd_subdistr (P Q R : StateRV Var) :
    `[fsl| [[P]] ⋆ (<e> ⬝ [[Q]] + ~<e> ⬝ [[R]])]
    ⊢ `[fsl| <e> ⬝ ([[P]] ⋆ [[Q]]) + ~<e> ⬝ ([[P]] ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [fslAdd, fslMul, fslReal, fslNot]
  apply le_trans (left_subdistr_of_unit _ _ _)
  apply truncatedAdd_le_truncatedAdd
  · rw [← mul_assoc, mul_comm _ (e s.stack), mul_assoc]
    apply unit_mul_le_mul le_rfl
    apply le_sSup
    use heap₁, heap₂
  · rw [← mul_assoc, mul_comm _ (σ <| e s.stack), mul_assoc]
    apply unit_mul_le_mul le_rfl
    apply le_sSup
    use heap₁, heap₂


theorem fslSepMul_fslMul_of_iverson_subdistr (P : State Var → Prop) (Q R : StateRV Var) :
    `[fsl| ⁅P⁆ ⋆ ([[Q]] ⬝ [[R]]) ⊢ (⁅P⁆ ⋆ [[Q]]) ⬝ (⁅P⁆ ⋆ [[R]])] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [fslMul, fslIverson]
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
  · apply unit_mul_le_mul
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rfl
    · apply le_sSup
      use heap₁, heap₂, h_disjoint, h_union
      rfl

theorem fslSepMul_fslSup_distr (P : StateRV Var) (Q : α → StateRV Var) :
    `[fsl| [[P]] ⋆ S (a : α). [[Q a]]] = `[fsl| S (a : α). [[P]] ⋆ [[Q a]]] := by
  funext s
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [mul_comm, ← unit_le_div_iff_mul_le, fslSup_apply]
    apply iSup_le
    intro x
    rw [unit_le_div_iff_mul_le, mul_comm, fslSup_apply, le_iSup_iff]
    intro _ h
    apply le_trans ?_ (h x); clear h
    apply le_sSup
    use heap₁, heap₂
  · rw [fslSup_apply]
    apply iSup_le
    intro x
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    apply le_sSup_of_le
    · use heap₁, heap₂, h_disjoint, h_union
    · apply unit_mul_le_mul le_rfl
      rw [fslSup_apply, le_iSup_iff]
      intro _ h
      exact le_trans le_rfl (h x)

theorem fslSepMul_fslInf_subdistr (P : StateRV Var) (Q : α → StateRV Var) :
    `[fsl| [[P]] ⋆ I (a : α). [[Q a]] ⊢ I (a : α). [[P]] ⋆ [[Q a]]] := by
  intro s
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  simp only [fslInf_apply, le_iInf_iff]
  intro x
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union
  · apply unit_mul_le_mul le_rfl
    exact iInf_le _ _

theorem fslSepDiv_fslMax_supdistr (P Q R : StateRV Var) :
    `[fsl| ([[P]] -⋆ [[Q]]) ⊔ ([[P]] -⋆ [[R]])] ⊢ `[fsl| [[P]] -⋆ ([[Q]] ⊔ [[R]])] := by
  intro s
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  apply sup_le
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply unit_div_le_div ?_ le_rfl
      simp only [fslMax]
      show _ ≤ Q ⟨s.stack, s.heap ∪ heap⟩ ⊔ R ⟨s.stack, s.heap ∪ heap⟩
      exact le_max_left _ _
  · apply sInf_le_of_le
    · use heap, h_disjoint
    · apply unit_div_le_div ?_ le_rfl
      simp only [fslMax]
      show _ ≤ Q ⟨s.stack, s.heap ∪ heap⟩ ⊔ R ⟨s.stack, s.heap ∪ heap⟩
      exact le_max_right _ _

theorem fslSepDiv_fslMin_distr (P Q R : StateRV Var) :
    `[fsl| ([[P]] -⋆ [[Q]]) ⊓ ([[P]] -⋆ [[R]])] = `[fsl| [[P]] -⋆ ([[Q]] ⊓ [[R]])] := by
  apply le_antisymm
  · intro s
    apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    rw [unit_le_div_iff_mul_le]
    apply le_inf
    · rw [← unit_le_div_iff_mul_le]
      simp only [fslMin]
      show `[fsl| [[P]] -⋆ [[Q]] ] s ⊓ `[fsl| [[P]] -⋆ [[R]] ] s ≤ _
      rw [min_le_iff]
      left
      apply sInf_le
      use heap, h_disjoint
    · rw [← unit_le_div_iff_mul_le]
      simp only [fslMin]
      show `[fsl| [[P]] -⋆ [[Q]] ] s ⊓ `[fsl| [[P]] -⋆ [[R]] ] s ≤ _
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
      · apply unit_div_le_div ?_ le_rfl
        simp only [fslMin]
        show Q ⟨s.stack, s.heap ∪ heap⟩ ⊓ R ⟨s.stack, s.heap ∪ heap⟩ ≤ _
        exact min_le_left _ _
    · apply le_sInf
      rintro _ ⟨heap, h_disjoint, rfl⟩
      apply sInf_le_of_le
      · use heap, h_disjoint
      · apply unit_div_le_div ?_ le_rfl
        simp only [fslMin]
        show Q ⟨s.stack, s.heap ∪ heap⟩ ⊓ R ⟨s.stack, s.heap ∪ heap⟩ ≤ _
        exact min_le_right _ _

theorem fslSepDiv_fslAdd_supdistr (P Q R : StateRV Var) :
    `[fsl| ([[P]] -⋆ [[Q]]) + ([[P]] -⋆ [[R]]) ⊢ [[P]] -⋆ ([[Q]] + [[R]])] := by
  intro s
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  simp only [fslAdd]
  apply le_trans ?_ (superdistr_of_unit_div _ _ _)
  apply truncatedAdd_le_truncatedAdd
  · apply sInf_le
    use heap
  · apply sInf_le
    use heap

theorem fslSepDiv_weight_fslAdd_subdistr (P Q R : StateRV Var) :
    `[fsl| <e> ⬝ ([[P]] -⋆ [[Q]]) + ~<e> ⬝ ([[P]] -⋆ [[R]])]
    ⊢ `[fsl| [[P]] -⋆ (<e> ⬝ [[Q]] + ~<e> ⬝ [[R]])] := by
  intro s
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  simp only [fslAdd, fslMul, fslReal, fslNot]
  apply le_trans ?_ (superdistr_of_unit_div _ _ _)
  apply truncatedAdd_le_truncatedAdd
  · apply le_trans ?_ unit_mul_div
    apply unit_mul_le_mul le_rfl
    apply sInf_le
    use heap
  · apply le_trans ?_ unit_mul_div
    apply unit_mul_le_mul le_rfl
    apply sInf_le
    use heap

theorem fslSepDiv_fslSup_superdistr (P : StateRV Var) (Q : α → StateRV Var) :
    `[fsl| S (a : α). [[P]] -⋆ [[Q a]] ⊢  [[P]] -⋆ S (a : α). [[Q a]]] := by
  intro s
  rw [fslSup_apply]
  apply iSup_le
  intro x
  apply le_sInf
  rintro _ ⟨heap, h_disjoint, rfl⟩
  rw [fslSup_apply]
  apply sInf_le_of_le
  · use heap, h_disjoint
  · apply unit_div_le_div ?_ le_rfl
    rw [le_iSup_iff]
    intro _ h
    exact le_trans le_rfl (h x)

theorem fslSepDiv_fslInf_distr (P : StateRV Var) (Q : α → StateRV Var) :
    `[fsl| I (a : α). [[P]] -⋆ [[Q a]]] = `[fsl| [[P]] -⋆ I (a : α). [[Q a]]] := by
  funext s
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    rw [fslInf_apply, fslInf_apply, unit_le_div_iff_mul_le]
    apply le_iInf
    intro x
    rw [← unit_le_div_iff_mul_le, iInf_le_iff]
    rintro _ h
    apply le_trans (h x) ?_
    apply sInf_le
    use heap
  · rw [fslInf_apply]
    apply le_iInf
    intro x
    apply le_sInf
    rintro _ ⟨heap, h_disjoint, rfl⟩
    apply sInf_le_of_le
    · use heap, h_disjoint
    · apply unit_div_le_div ?_ le_rfl
      rw [fslInf_apply, iInf_le_iff]
      intro _ h
      exact le_trans (h x) le_rfl

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
    show `[fsl| [[P]] ⋆ [[Q]] ] s ⊓ `[fsl| [[P]] ⋆ [[R]] ] s
        ≤ _ * (Q ⟨s.stack, heap₂⟩ ⊓ R ⟨s.stack, heap₂⟩)
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

open Syntax in
theorem fslSepMul_weight_fslAdd_distr_of_precise (e : ProbExp Var) (P Q R : StateRV Var) (h : precise P) :
    `[fsl| [[P]] ⋆ (<e> ⬝ [[Q]] + ~<e> ⬝ [[R]])] = `[fsl| <e> ⬝ ([[P]] ⋆ [[Q]]) + ~<e> ⬝ ([[P]] ⋆ [[R]])] := by
  apply le_antisymm (fslSepMul_weight_fslAdd_subdistr P Q R)
  intro s
  obtain ⟨heap₁, h_subset, h⟩ := h s
  obtain ⟨heap₂, h_disjoint, h_union⟩ := union_of_subset h_subset
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union.symm
  · simp only [fslAdd, fslMul, fslReal, fslNot]
    rw [left_distrib_of_unit]
    swap
    · exact weighted_is_unit _ _ _
    · apply truncatedAdd_le_truncatedAdd
      · rw [← mul_assoc, mul_comm _ (e s.stack), mul_assoc]
        apply unit_mul_le_mul le_rfl
        apply sSup_le
        rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
        cases eq_or_ne heap₁ heap₁'
        case inl h_eq =>
          rw [h_eq] at h_union h_disjoint ⊢
          apply unit_mul_le_mul le_rfl
          have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
          rw [this]
        case inr h_neq =>
          specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
          rw [h]
          simp only [zero_mul, zero_le]
      · rw [← mul_assoc, mul_comm _ (σ <| e s.stack), mul_assoc]
        apply unit_mul_le_mul le_rfl
        apply sSup_le
        rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
        cases eq_or_ne heap₁ heap₁'
        case inl h_eq =>
          rw [h_eq] at h_union h_disjoint ⊢
          apply unit_mul_le_mul le_rfl
          have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
          rw [this]
        case inr h_neq =>
          specialize h heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
          rw [h]
          simp only [zero_mul, zero_le]

theorem fslSepMul_fslInf_distr_of_precise
    (P : StateRV Var) (Q : α → StateRV Var) (h : precise P) [Nonempty α] :
    `[fsl| [[P]] ⋆ I (a : α). [[Q a]]] = `[fsl| I (a : α). [[P]] ⋆ [[Q a]]] := by
  apply le_antisymm (fslSepMul_fslInf_subdistr P Q)
  intro s
  obtain ⟨heap₁, h_subset, h_prec⟩ := h s
  obtain ⟨heap₂, h_disjoint, h_union⟩ := union_of_subset h_subset
  apply le_sSup_of_le
  · use heap₁, heap₂, h_disjoint, h_union.symm
  · simp only [fslInf_apply]
    rw [mul_iInf]
    apply le_iInf
    intro a
    rw [iInf_le_iff]
    rintro _ h
    apply le_trans (h a)
    apply sSup_le
    rintro _ ⟨heap₁', heap₂', h_disjoint', h_union', rfl⟩
    cases eq_or_ne heap₁ heap₁'
    case inl h_eq =>
      rw [h_eq] at h_disjoint h_union ⊢
      apply unit_mul_le_mul le_rfl
      have := eq_of_union_of_union_left h_disjoint h_union h_disjoint' h_union'.symm
      rw [this]
    case inr h_neq =>
      specialize h_prec heap₁' (subset_of_union h_disjoint' h_union'.symm) h_neq
      simp only [h_prec, zero_mul, zero_le]

end Precise

section Pure

theorem pure_fslEquals : pure `[fsl| e === e'] := by
  intro s heap₁ heap₂
  simp only [fslEquals]

theorem pure_fslIverson_slEquals : pure `[fsl| ⁅e === e'⁆] := by
  intro s heap₁ heap₂
  simp only [fslIverson, SL.slEquals]

theorem pure_fslIverson_slExp : pure `[fsl| ⁅<e>⁆] := by
  intro s heap₁ heap₂
  simp only [fslIverson, SL.slExp]

theorem pure_fslMul (h_P : pure P) (h_Q : pure Q) : pure `[fsl| [[P]] ⬝ [[Q]]] := by
  intro s heap₁ heap₂
  simp only [fslMul, h_P s heap₁ heap₂, h_Q s heap₁ heap₂]

theorem fslMul_fslSepMul_of_pure {P Q R : StateRV Var} (h : pure P) :
    `[fsl| [[P]] ⬝ [[Q]] ⋆ [[R]]] = `[fsl| ([[P]] ⬝ [[Q]]) ⋆ [[R]]] := by
  apply le_antisymm
  · intro s
    simp only [fslMul]
    rw [mul_comm, ← unit_le_div_iff_mul_le]
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [unit_le_div_iff_mul_le, mul_comm, ← mul_assoc]
    apply le_sSup
    use heap₁, heap₂, h_disjoint, h_union
    simp only [fslMul, mul_eq_mul_right_iff]
    left; left
    exact h s.stack s.heap heap₁
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_dijoint, h_union, rfl⟩
    simp only [fslMul]
    rw [mul_assoc]
    apply unit_mul_le_mul
    · rw [h]
    · apply le_sSup
      use heap₁, heap₂

theorem fslMul_eq_emp_fslSepMul_of_pure {P Q : StateRV Var} (h : pure P) :
    `[fsl| [[P]] ⬝ [[Q]]] = `[fsl| ([[P]] ⊓ emp) ⋆ [[Q]]] := by
  apply le_antisymm
  · intro s
    apply le_sSup
    use ∅, s.heap, emptyHeap_disjoint', emptyHeap_union'
    rw [fslMin, Pi.inf_apply, fslEmp, iteOneZero_pos rfl, fslMul]
    rw [h s.stack ∅ s.heap]
    rw [mul_eq_mul_right_iff, left_eq_inf]
    left; exact le_one'
  · intro s
    apply sSup_le
    rintro i ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    rw [fslMin, Pi.inf_apply, fslEmp, iteOneZero_eq_ite, fslMul]
    split_ifs
    case pos h_emp =>
      apply unit_mul_le_mul
      · rw [inf_le_iff]
        left
        rw [h s.stack heap₁ s.heap]
      · rw [h_emp, emptyHeap_union] at h_union
        rw [h_union]
    case neg =>
      simp only [zero_le, inf_of_le_right, zero_mul]

theorem fslSepMul_fslTrue_of_pure {P : StateRV Var} (h : pure P) :
    `[fsl| [[P]] ⋆ fTrue] = P := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    simp only [fslTrue, mul_one]
    rw [h s.stack s.heap heap₁]
  · intro s
    apply le_sSup
    use ∅, s.heap, emptyHeap_disjoint', emptyHeap_union'
    simp only [fslTrue, mul_one]
    rw [h s.stack s.heap ∅]

theorem fslSepMul_eq_fslTrue_fslMul_of_pure {P Q : StateRV Var} (h : pure P) :
    `[fsl| [[P]] ⋆ [[Q]]] = `[fsl| fTrue ⋆ ([[P]] ⬝ [[Q]])] := by
  apply le_antisymm
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    apply le_sSup
    use heap₁, heap₂, h_disjoint, h_union
    simp only [fslTrue, fslMul, one_mul, mul_eq_mul_right_iff]
    left
    exact h s.stack heap₁ heap₂
  · intro s
    apply sSup_le
    rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
    apply le_sSup
    use heap₁, heap₂, h_disjoint, h_union
    simp only [fslTrue, fslMul, one_mul, mul_eq_mul_right_iff]
    left
    exact h s.stack heap₂ heap₁


end Pure

end FSL
