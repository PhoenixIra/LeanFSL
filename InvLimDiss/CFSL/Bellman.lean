import InvLimDiss.CFSL.Step
import InvLimDiss.CFSL.WeakExpectation
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-! This file contains the equviality theorem for the bellman-solution and the concurrent
bellman-solution.

`wrle_of_emp_eq_bellman` states this equality. -/

namespace Bellman

open FSL Syntax OrderHom unitInterval Atom Semantics CFSL

variable {Var : Type}

/-- We introduce the abbreviation `semantics` for the probability transition function. -/
noncomputable abbrev semantics := @programSmallStepSemantics Var

/-- One step in the probability transition function -- essentially the bellman-operator. -/
noncomputable def bstep (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : (Program Var) × (State Var), (semantics c s a cs.1 cs.2) * inner cs.1 cs.2 = x}

theorem bstep_mono (c : Program Var) : Monotone (bstep c) := by
  intro X X' h_X
  intro s
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  have : ∑' cs : (Program Var) × (State Var), (semantics c s a cs.1 cs.2) * X cs.1 cs.2
    ∈ { x | ∃ a ∈ enabledAction c s,
      ∑' cs : (Program Var) × (State Var), (semantics c s a cs.1 cs.2) * X cs.1 cs.2 = x} := by {
        use a
      }
  apply sInf_le_of_le this; clear this
  apply Summable.tsum_mono (isSummable _) (isSummable _)
  intro cs
  simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state]
  cases eq_or_ne (semantics c s a cs.1 cs.2) 0 with
  | inl h_eq =>
    rw [h_eq, zero_mul, zero_mul]
  | inr h_ne =>
    rw [Subtype.mk_le_mk, Set.Icc.coe_mul, Set.Icc.coe_mul]
    rw [mul_le_mul_left]
    · apply h_X
    · apply lt_of_le_of_ne nonneg'
      exact Ne.symm h_ne

private lemma tsum_subtype' [TopologicalSpace β] [AddCommMonoid β]
    (f : α → β) (P : α → Prop) :
    ∑' s : { x : α // P x}, f s = ∑' s : α, Set.indicator { x | P x} f s := by
  apply tsum_subtype

theorem step_le_bstep {c : Program Var} (h : cp₁ ≤ cp₂):
    step c cp₁ ≤ bstep c cp₂ := by
  rw [Pi.le_def]; intro s
  rw [step, bstep]
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  apply sInf_le_of_le
  · use a, h_a
  · rw [tsum_subtype' (fun cs => CFSL.semantics _ _ _ _ _ * cp₁ _ _)]
    apply Summable.tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]; intro cs
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs
    case pos h_neq => exact unit_mul_le_mul le_rfl (h cs.1 cs.2)
    case neg h_eq => exact nonneg'

theorem bstep_le_step {c : Program Var} (h : cp₁ ≤ cp₂) (h_abort : ∀ s, cp₁ [Prog| ↯] s = 0) :
    bstep c cp₁ ≤ step c cp₂ := by
  rw [Pi.le_def]; intro s
  rw [step, bstep]
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  apply sInf_le_of_le
  · use a, h_a
  · rw [tsum_subtype' (fun cs => CFSL.semantics _ _ _ _ _ * cp₂ _ _)]
    apply Summable.tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]; intro cs
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs
    case pos h_neq => exact unit_mul_le_mul le_rfl (h cs.1 cs.2)
    case neg h_eq =>
      rw [ne_eq, not_not] at h_eq
      rw [h_eq, h_abort cs.2]
      simp only [mul_zero, le_refl]

/-- The bellman-operator.-/
noncomputable def bellmanStep (post : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[fsl| fFalse]
  | X, program => `[fsl| [[bstep program (fun c => `[fsl| [[X c]]]) ]] ]

theorem bellman_monotone (post : StateRV Var) : Monotone (bellmanStep post) := by
  intro X X' h_X
  unfold bellmanStep
  rw [Pi.le_def]
  intro c
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply bstep_mono c
    exact h_X

noncomputable def bellmanStepHom (post : StateRV Var) :
    (Program Var → StateRV Var) →o (Program Var → StateRV Var) :=
  ⟨bellmanStep post, bellman_monotone post⟩

/-- greatest solution of the bellman equation -/
noncomputable def bellmanSolution (post : StateRV Var) : (Program Var → StateRV Var) :=
    gfp (bellmanStepHom post)

open OrderHom

open OrdinalApprox in
theorem gfp_wrle_eq_gfp_bellman {post : StateRV Var} :
    gfp (wrleStepHom post `[fsl|emp])
    = gfp (bellmanStepHom post) := by
  apply le_antisymm
  · rw [← gfpApprox_ord_eq_gfp, ← gfpApprox_ord_eq_gfp]
    simp only [wrleStepHom, bellmanStepHom]
    induction (Order.succ (Cardinal.mk _)).ord using Ordinal.induction with
    | h i ih =>
      unfold gfpApprox
      apply le_sInf
      simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
        sInf_insert, le_top, inf_of_le_right, forall_eq_or_imp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, true_and]
      intro j h_j
      apply sInf_le_of_le
      · simp only [Set.mem_setOf_eq]
        use j, h_j
      · simp only [coe_mk]
        rw [Pi.le_def]; intro c
        unfold wrleStep bellmanStep
        split
        case a.h.a.h.h_1 => rfl
        case a.h.a.h.h_2 => rfl
        case a.h.a.h.h_3 =>
          unfold wrleStep bellmanStep at ih
          simp only [fslSepMul_fslEmp_eq, fslEmp_fslSepDiv_eq] at ih ⊢
          apply step_le_bstep
          rw [Pi.le_def]; intro c
          exact ih j h_j c
  · rw [← OrderHom.map_gfp]
    rw [← gfpApprox_ord_eq_gfp, ← gfpApprox_ord_eq_gfp]
    simp only [wrleStepHom, bellmanStepHom]
    induction (Order.succ (Cardinal.mk _)).ord using Ordinal.induction with
    | h i ih =>
      unfold gfpApprox
      apply le_sInf
      simp only [coe_mk, exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
        sInf_insert, le_top, inf_of_le_right, forall_eq_or_imp, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, true_and]
      intro j h_j
      rw [Pi.le_def]; intro c
      unfold bellmanStep wrleStep
      split
      case a.h.a.h_1 => rfl
      case a.h.a.h_2 => rfl
      case a.h.a.h_3 =>
        unfold bellmanStep wrleStep at ih
        simp only [fslSepMul_fslEmp_eq, fslEmp_fslSepDiv_eq] at ih ⊢
        apply bstep_le_step
        · rw [Pi.le_def]; intro c
          apply sInf_le_of_le
          · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
              exists_exists_and_eq_and]
            use j, h_j
          · exact ih j h_j c
        · intro s
          apply le_antisymm ?_ nonneg'
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
            exists_exists_and_eq_and]
          use j, h_j
          rfl

theorem wrle_of_emp_eq_bellman {c : Program Var} {post : StateRV Var} :
    `[fsl| wrle [c] ([[post]] | emp)] = bellmanSolution post c := by
  unfold wrle' bellmanSolution
  apply congrFun
  exact gfp_wrle_eq_gfp_bellman



end Bellman
