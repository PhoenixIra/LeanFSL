import InvLimDiss.SL.Framing.Basic
import InvLimDiss.SL.Quantitative
import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.Mathlib.FixedPoints

namespace CQSL

open Syntax OrdinalApprox QSL State unitInterval

private theorem step_eq_of_not_mem_vars {c : Program Vars} {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource) (h_i' : i' < i)
    (h_ind : ∀ k < i, ∀ {c : Program Vars} {s : State Vars}, v ∉ varProg c ∪ varRV P ∪ varRV resource →
      gfpApprox (wrle_step_hom P resource) ⊤ k c s
      = gfpApprox (wrle_step_hom P resource) ⊤ k c ⟨substituteVar s.stack v q, s.heap⟩) :
    step c (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step c (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  sorry

private theorem gfpApprox_eq_of_not_mem_vars
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource) :
    gfpApprox (wrle_step_hom P resource) ⊤ i c s
    = gfpApprox (wrle_step_hom P resource) ⊤ i c ⟨substituteVar s.stack v q, s.heap⟩ := by
  induction i using Ordinal.induction generalizing c s with
  | h i ih =>
    have h_vars := h
    simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
      Decidable.not_not] at h
    obtain ⟨⟨_, h_P⟩, h_resource⟩ := h
    unfold gfpApprox
    rw [sInf_apply, iInf_apply, iInf_apply]
    apply congrArg
    apply funext
    simp only [Subtype.forall, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, forall_eq_or_imp, Pi.top_apply, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · rfl
    · intro i' h_i'
      rw [wrle_step_hom, OrderHom.coe_mk, wrle_step]
      cases eq_or_ne c [Prog| ↓] with
      | inl h_term =>
        rw [h_term]
        simp only
        rw [h_P _ q]
      | inr h_neq_term =>
        cases eq_or_ne c [Prog| ↯] with
        | inl h_abort =>
          rw [h_abort]
          rfl
        | inr h_neq_abort =>
          simp only [qslSepDiv]
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            rw [h_resource _ q]
          }
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            right; right; left; left; intro c
            change `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]
          }
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            rw [step_eq_of_not_mem_vars _ h_vars h_i' ih]
          }
          rfl

theorem varRV_of_gfpApprox_wrle_step {P resource : StateRV Var} :
    varRV (gfpApprox (wrle_step_hom P resource) ⊤ i c)
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  exact gfpApprox_eq_of_not_mem_vars h_v

theorem varRV_of_wrle :
    varRV `[qsl Var| wrle [c] ([[P]]|[[resource]])]
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, State.substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  unfold wrle'
  rw [← gfpApprox_ord_eq_gfp]
  exact gfpApprox_eq_of_not_mem_vars h_v


end CQSL
