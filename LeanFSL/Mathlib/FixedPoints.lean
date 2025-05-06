import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import Mathlib.Order.OmegaCompletePartialOrder

variable [CompleteLattice α]

theorem OrdinalApprox.gfpApprox_le_gfpApprox_of_le (f g : α →o α) (h : f ≤ g) :
    gfpApprox f ≤ gfpApprox g := by
  intro x i
  induction i using Ordinal.induction with
  | h i ih =>
    unfold gfpApprox
    apply le_sInf
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sInf_insert,
      forall_eq_or_imp, inf_le_left, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      true_and]
    intro i' h_lt
    apply inf_le_of_right_le
    apply sInf_le_of_le
    · use i'
    · apply le_trans (h _)
      simp only [OrderHom.toFun_eq_coe]
      apply g.monotone
      exact ih i' h_lt

open OmegaCompletePartialOrder

lemma ωSup_eq_iSup (c : Chain α) : ωSup c = ⨆ n : ℕ, c n := rfl
lemma ofDual_dual_chain (c : Chain αᵒᵈ) (n : ℕ) : OrderDual.ofDual (c n) = c.toFun n := rfl

theorem dual_continuous_iff_co_continuous (f : α →o α) :
    ωScottContinuous (OrderHom.dual f) ↔
    ∀ c : ℕ → α, Antitone c → f (⨅ n : ℕ, c n) = ⨅ n : ℕ, f (c n) := by
  apply Iff.intro
  · intro h c h_c
    rw [ωScottContinuous_iff_map_ωSup_of_orderHom] at h
    let c' : Chain αᵒᵈ := ⟨c, h_c⟩
    specialize h c'
    simp only [ωSup_eq_iSup, OrderHom.dual_apply_coe, Function.comp_apply, ofDual_iSup,
      ofDual_dual_chain, OrderHom.toFun_eq_coe, Chain.map_coe, OrderHom.coe_mk] at h
    rw [← toDual_iInf, OrderDual.toDual_inj] at h
    exact h
  · intro h
    rw [ωScottContinuous_iff_map_ωSup_of_orderHom]
    intro c'
    specialize h c'.toFun c'.monotone
    simp only [ωSup_eq_iSup, OrderHom.dual_apply_coe, Function.comp_apply, ofDual_iSup,
      ofDual_dual_chain, OrderHom.toFun_eq_coe, Chain.map_coe]
    rw [← toDual_iInf, OrderDual.toDual_inj]
    exact h
