import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Framing.Basic

/-! Approximations for the variables in a random variable -/

namespace FSL

open Syntax Semantics FSL State unitInterval


theorem varRV_of_fslTrue : varRV `[fsl Var| fTrue] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_fslFalse : varRV `[fsl Var| fFalse] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_fslEmp : varRV `[fsl Var| emp] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_fslPointsTo :
    varRV `[fsl Var| e ↦ e'] ⊆ (varValue e) ∪ (varValue e') := by
  intro v h_v
  contrapose h_v
  simp only [varValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_e, h_e'⟩ := h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [fslPointsTo]
  rw [h_e s.stack q, h_e' s.stack q]

theorem varRV_of_fslEquals :
    varRV `[fsl Var| e = e'] ⊆ (varValue e) ∪ (varValue e') := by
  intro v h_v
  contrapose h_v
  simp only [varValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_e, h_e'⟩ := h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [fslEquals]
  rw [h_e s.stack q, h_e' s.stack q]

theorem varRV_of_fslReal :
    varRV `[fsl Var| <e>] = varProb e := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varProb, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    intro s q
    simp only [fslReal]
    rw [h_v s.stack q]
  · intro h_v
    contrapose h_v
    simp only [varRV, fslReal, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not] at h_v
    simp only [varProb, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    intro s q
    rw [h_v ⟨s, ∅⟩ q]

theorem varRV_of_fslIverson :
    varRV `[fsl Var| ⁅P⁆] = varProp P := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varProp, substituteStack, ne_eq, eq_iff_iff, Set.mem_setOf_eq, not_exists,
      not_not] at h_v
    simp only [varRV, fslIverson, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not]
    intro s q
    rw [h_v s q]
  · intro h_v
    contrapose h_v
    simp only [varRV, fslIverson, substituteStack, ne_eq, iteOneZero_eq_iteOneZero_iff,
      Set.mem_setOf_eq, not_exists, not_not] at h_v
    simp only [varProp, substituteStack, ne_eq, eq_iff_iff, Set.mem_setOf_eq, not_exists, not_not]
    intro s q
    exact h_v s q

theorem varRV_of_fslSubst :
    varRV `[fsl Var| [[f]](v ↦ e)] ⊆ varRV f \ {v} ∪ varValue e := by
  intro v' h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q'
  simp only [fslSubst, substituteStack]
  cases eq_or_ne v v' with
  | inl h_eq =>
    simp only [varRV, substituteStack, ne_eq, h_eq, varValue, Set.mem_union, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff, not_true_eq_false, and_false, false_or, not_exists,
      Decidable.not_not] at h_v
    rw [substituteVar_substituteVar_of_eq h_eq.symm]
    rw [h_v s.stack q']
  | inr h_neq =>
    simp only [varRV, substituteStack, ne_eq, varValue, Set.mem_union, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff, h_neq.symm, not_false_eq_true, and_true, not_or,
      not_exists, Decidable.not_not] at h_v
    obtain ⟨h_f, h_e⟩ := h_v
    rw [h_e s.stack q', substituteVar_substituteVar_of_neq h_neq.symm]
    exact h_f ⟨substituteVar s.stack v (e s.stack), s.heap⟩ q'

theorem varRV_of_fslNot :
    varRV `[fsl Var| ~[[f]]] = varRV f := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varRV, fslNot, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not]
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
    intro s q
    rw [h_v s q]
  · intro h_v
    contrapose h_v
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    simp only [varRV, fslNot, substituteStack, ne_eq, symm_eq_symm_iff_eq, Set.mem_setOf_eq,
      not_exists, Decidable.not_not] at h_v
    intro s q
    exact h_v s q

theorem varRV_of_fslMin :
    varRV `[fsl Var| [[f]] ⊓ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslMin, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  show f _ ⊓ g _ = f _ ⊓ g _
  rw [h_f s q, h_g s q]

theorem varRV_of_fslMax :
    varRV `[fsl Var| [[f]] ⊔ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslMax, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  show f _ ⊔ g _ = f _ ⊔ g _
  rw [h_f s q, h_g s q]

theorem varRV_of_fslAdd :
    varRV `[fsl Var| [[f]] + [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslAdd, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_fslMul :
    varRV `[fsl Var| [[f]] ⬝ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslMul, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_fslSup {f : α → StateRV Var} :
    varRV `[fsl Var| S x. [[f x]]] ⊆ { v | ∃ x, v ∈ varRV (f x)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslSup, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  rw [iSup_apply, iSup_apply]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
  conv => left; right; intro x; rw [h_v x s q]

theorem varRV_of_fslInf {f : α → StateRV Var} :
    varRV `[fsl Var| I x. [[f x]]] ⊆ { v | ∃ x, v ∈ varRV (f x)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslInf, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  rw [iInf_apply, iInf_apply]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
  conv => left; right; intro x; rw [h_v x s q]

theorem varRV_of_fslSepMul :
    varRV `[fsl Var| [[f]] ⋆ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslSepMul, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  intro s q
  conv => left; right; intro i; left; intro i; right; intro h₁; right; intro h₂; rw [h_f _ q, h_g _ q]

theorem varRV_of_fslBigSepMul {f : ℕ → StateRV Var}:
    varRV `[fsl Var| [⋆] n ∈ { ... m}. [[f n]]] ⊆ { v | ∃ i < m, v ∈ varRV (f i)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, not_and,
    Decidable.not_not] at h_v
  intro s q
  induction m generalizing s with
  | zero => simp only [fslBigSepMul, fslEmp]
  | succ m' ih =>
    simp only [fslBigSepMul, fslSepMul]
    conv => left; right; intro i; left; intro i; right; intro h₁; rw [h_v m' (by simp) _ q]
    have : (∀ n < m', ∀ (s : State Var) (q : ℚ),
        f n s = f n { stack := substituteVar s.stack v q, heap := s.heap }) := by {
      intro n h_n s q
      rw [h_v n ?_ s q]
      exact Nat.lt_add_right 1 h_n
    }
    conv => left; right; intro i; left; intro i; right; intro h₁; right; intro h₂; rw [ih this _]

theorem varRV_of_fslSepDiv :
    varRV `[fsl Var| [[f]] -⋆ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, fslSepDiv, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  intro s q
  conv => left; right; intro i; left; intro i; right; intro h'; rw [h_f _ q, h_g _ q]

end FSL
