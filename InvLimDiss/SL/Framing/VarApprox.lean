import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Framing.Basic

/-! Approximations for the variables in a random variable -/

namespace QSL

open Syntax Semantics QSL State unitInterval


theorem varRV_of_qslTrue : varRV `[qsl Var| qTrue] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_qslFalse : varRV `[qsl Var| qFalse] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_qslEmp : varRV `[qsl Var| emp] = ∅ := by
  rw [varRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varRV_of_qslPointsTo :
    varRV `[qsl Var| e ↦ e'] ⊆ (varsValue e) ∪ (varsValue e') := by
  intro v h_v
  contrapose h_v
  simp only [varsValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_e, h_e'⟩ := h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [qslPointsTo]
  rw [h_e s.stack q, h_e' s.stack q]

theorem varRV_of_qslEquals :
    varRV `[qsl Var| e = e'] ⊆ (varsValue e) ∪ (varsValue e') := by
  intro v h_v
  contrapose h_v
  simp only [varsValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_e, h_e'⟩ := h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [qslEquals]
  rw [h_e s.stack q, h_e' s.stack q]

theorem varRV_of_qslReal :
    varRV `[qsl Var| <e>] = varsProb e := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varsProb, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    intro s q
    simp only [qslReal]
    rw [h_v s.stack q]
  · intro h_v
    contrapose h_v
    simp only [varRV, qslReal, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not] at h_v
    simp only [varsProb, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    intro s q
    rw [h_v ⟨s, ∅⟩ q]

theorem varRV_of_qslIverson :
    varRV `[qsl Var| ⁅P⁆] = varProp P := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varProp, substituteStack, ne_eq, eq_iff_iff, Set.mem_setOf_eq, not_exists,
      not_not] at h_v
    simp only [varRV, qslIverson, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not]
    intro s q
    rw [h_v s q]
  · intro h_v
    contrapose h_v
    simp only [varRV, qslIverson, substituteStack, ne_eq, iteOneZero_eq_iteOneZero_iff,
      Set.mem_setOf_eq, not_exists, not_not] at h_v
    simp only [varProp, substituteStack, ne_eq, eq_iff_iff, Set.mem_setOf_eq, not_exists, not_not]
    intro s q
    exact h_v s q

theorem varRV_of_qslSubst :
    varRV `[qsl Var| [[f]](v ↦ e)] ⊆ varRV f \ {v} ∪ varsValue e := by
  intro v' h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q'
  simp only [qslSubst, substituteStack]
  cases eq_or_ne v v' with
  | inl h_eq =>
    simp only [varRV, substituteStack, ne_eq, h_eq, varsValue, Set.mem_union, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff, not_true_eq_false, and_false, false_or, not_exists,
      Decidable.not_not] at h_v
    rw [substituteVar_substituteVar_of_eq h_eq.symm]
    rw [h_v s.stack q']
  | inr h_neq =>
    simp only [varRV, substituteStack, ne_eq, varsValue, Set.mem_union, Set.mem_diff,
      Set.mem_setOf_eq, Set.mem_singleton_iff, h_neq.symm, not_false_eq_true, and_true, not_or,
      not_exists, Decidable.not_not] at h_v
    obtain ⟨h_f, h_e⟩ := h_v
    rw [h_e s.stack q', substituteVar_substituteVar_of_neq h_neq.symm]
    exact h_f ⟨substituteVar s.stack v (e s.stack), s.heap⟩ q'

theorem varRV_of_qslNot :
    varRV `[qsl Var| ~[[f]]] = varRV f := by
  apply Set.ext
  intro v
  apply Iff.intro
  · intro h_v
    contrapose h_v
    simp only [varRV, qslNot, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
      Decidable.not_not]
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
    intro s q
    rw [h_v s q]
  · intro h_v
    contrapose h_v
    simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
    simp only [varRV, qslNot, substituteStack, ne_eq, symm_eq_symm_iff_eq, Set.mem_setOf_eq,
      not_exists, Decidable.not_not] at h_v
    intro s q
    exact h_v s q

theorem varRV_of_qslMin :
    varRV `[qsl Var| [[f]] ⊓ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslMin, Inf.inf, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_qslMax :
    varRV `[qsl Var| [[f]] ⊔ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslMax, Sup.sup, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_qslAdd :
    varRV `[qsl Var| [[f]] + [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslAdd, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_qslMul :
    varRV `[qsl Var| [[f]] ⬝ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslMul, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  rw [h_f s q, h_g s q]

theorem varRV_of_qslSup {f : α → StateRV Var} :
    varRV `[qsl Var| S x. [[f x]]] ⊆ { v | ∃ x, v ∈ varRV (f x)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslSup, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  rw [iSup_apply, iSup_apply]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
  conv => left; right; intro x; rw [h_v x s q]

theorem varRV_of_qslInf {f : α → StateRV Var} :
    varRV `[qsl Var| I x. [[f x]]] ⊆ { v | ∃ x, v ∈ varRV (f x)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslInf, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  rw [iInf_apply, iInf_apply]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_v
  conv => left; right; intro x; rw [h_v x s q]

theorem varRV_of_qslSepMul :
    varRV `[qsl Var| [[f]] ⋆ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslSepMul, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  intro s q
  conv => left; right; intro i; left; intro i; right; intro h₁; right; intro h₂; rw [h_f _ q, h_g _ q]

theorem varRV_of_qslBigSepMul {f : ℕ → StateRV Var}:
    varRV `[qsl Var| [⋆] n ∈ { ... m}. [[f n]]] ⊆ { v | ∃ i < m, v ∈ varRV (f i)} := by
  intro v h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, not_and,
    Decidable.not_not] at h_v
  intro s q
  induction m generalizing s with
  | zero => simp only [qslBigSepMul, qslEmp]
  | succ m' ih =>
    simp only [qslBigSepMul, qslSepMul]
    conv => left; right; intro i; left; intro i; right; intro h₁; rw [h_v m' (by simp) _ q]
    have : (∀ n < m', ∀ (s : State Var) (q : ℚ),
        f n s = f n { stack := substituteVar s.stack v q, heap := s.heap }) := by {
      intro n h_n s q
      rw [h_v n ?_ s q]
      exact Nat.lt_add_right 1 h_n
    }
    conv => left; right; intro i; left; intro i; right; intro h₁; right; intro h₂; rw [ih this _]

theorem varRV_of_qslSepDiv :
    varRV `[qsl Var| [[f]] -⋆ [[g]]] ⊆ varRV f ∪ varRV g := by
  intro v h_v
  contrapose h_v
  simp only [varRV, qslSepDiv, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists,
    Decidable.not_not]
  simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h_v
  obtain ⟨h_f, h_g⟩ := h_v
  intro s q
  conv => left; right; intro i; left; intro i; right; intro h'; rw [h_f _ q, h_g _ q]

end QSL
