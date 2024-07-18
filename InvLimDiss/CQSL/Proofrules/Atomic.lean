import InvLimDiss.CQSL.WeakPre
import InvLimDiss.SL.Framing.Simps
import InvLimDiss.CQSL.Step.Framing

/-!
  Proofrules for wrlp with atomic programs as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics

private theorem support_wrlp_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : reachState Var =>
      programSmallStepSemantics c s a cs.prog cs.state
      * (`[qsl| (wrlp [cs.prog] ([[P]] ⋆ [[resource]] | emp )) ⋆ emp ] cs.state))
    ⊆ { cs : reachState Var | cs.prog = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_qsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.prog
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrlp_eq_of_abort, qslSepMul_qslEmp_eq, qslFalse] at h_qsl
      simp only [not_true_eq_false] at h_qsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.state

private theorem support_wrlp'_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : reachState Var =>
      programSmallStepSemantics c s a cs.prog cs.state
      * (`[qsl| (wrlp [cs.prog] ([[P]] | [[resource]] )) ⋆ [[resource]] ] cs.state))
    ⊆ { cs : reachState Var | cs.prog = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_qsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.prog
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrlp_eq_of_abort, qslSepMul_comm, qslSepMul_qslFalse_eq, qslFalse] at h_qsl
      simp only [not_true_eq_false] at h_qsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.state

theorem wrlp_atom (h : `[qsl| [[P]] ⋆ [[resource]] ⊢ wrlp [c] ([[P]] ⋆ [[resource]] | emp)])
    (h_atom : atomicProgram c) :
    `[qsl| [[P]] ⊢ wrlp [c] ([[P]] | [[resource]])] := by
  have := atomic_not_final h_atom
  rw [wrlp_eq_of_not_final this, le_qslSepDiv_iff_qslSepMul_le]
  apply le_trans h
  rw [wrlp_eq_of_not_final this, qslEmp_qslSepDiv_eq, Pi.le_def]
  intro s
  simp only [step, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a h_a
  apply sInf_le
  use a, h_a
  rw[← tsum_subtype_eq_of_support_subset <| support_wrlp_of_atom h_atom s P resource]
  rw[← tsum_subtype_eq_of_support_subset <| support_wrlp'_of_atom h_atom s P resource]
  apply le_antisymm
  · apply tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (programSmallStepSemantics c s a cs.val.prog cs.val.state) 0 with
    | inl h_zero =>
      rw [h_zero]
      simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_nzero =>
      apply unit_mul_le_mul le_rfl
      have := cs.prop
      simp only [Set.mem_setOf_eq] at this
      rw [this, wrlp_eq_of_term, wrlp_eq_of_term, qslSepMul_qslEmp_eq]
  · apply tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (programSmallStepSemantics c s a cs.val.prog cs.val.state) 0 with
    | inl h_zero =>
      rw [h_zero]
      simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_nzero =>
      apply unit_mul_le_mul le_rfl
      have := cs.prop
      simp only [Set.mem_setOf_eq] at this
      rw [this, wrlp_eq_of_term, wrlp_eq_of_term, qslSepMul_qslEmp_eq]

theorem wrlp_skip : `[qsl| [[P]] ⊢ wrlp [ [Prog| skip] ] ([[P]] | [[RI]])] := by
  rw [wrlp_eq_of_not_final (by simp only [finalProgram, Bool.false_eq_true, not_false_eq_true])]
  rw [le_qslSepDiv_iff_qslSepMul_le, Pi.le_def]
  intro s
  rw [step_skip, wrlp_eq_of_term]

theorem wrlp_assign (h : x ∉ varStateRV RI) :
    `[qsl| [[P]](x ↦ e) ⊢ wrlp [ [Prog| x ≔ e] ] ([[P]] | [[RI]])] := by
  rw [wrlp_eq_of_not_final (by simp only [finalProgram, Bool.false_eq_true, not_false_eq_true])]
  rw [le_qslSepDiv_iff_qslSepMul_le, Pi.le_def]
  intro s
  rw [step_assign, wrlp_eq_of_term]
  have : `[qsl| [[P]] ⋆ [[RI]]]  (s.substituteStack x (e s.stack))
    = `[qsl| ([[P]] ⋆ [[RI]])(x ↦ e)] s := rfl
  rw [this, substituteStack_of_qslSepCon e h]

open HeapValue State

theorem wrlp_mutate :
    `[qsl| (S (q : ℚ). e_loc ↦ q) ⋆ (e_loc ↦ e_val -⋆ [[P]])
          ⊢ wrlp [ [Prog| e_loc *≔ e_val] ] ([[P]] | [[RI]])] := by
  rw [wrlp_eq_of_not_final (by simp only [finalProgram, Bool.false_eq_true, not_false_eq_true])]
  rw [le_qslSepDiv_iff_qslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [writtenVarProgram, Set.empty_inter]
  · refine monotone_qslSepMul ?_ le_rfl
    intro s
    by_cases ∃ l : ℕ+, e_loc s.stack = l ∧ s.heap l ≠ undef
    case pos h_alloc =>
      obtain ⟨l, h_loc, h_alloc⟩ := h_alloc
      rw [step_mutate s _ h_loc h_alloc, wrlp_eq_of_term]
      simp only [State.substituteHeap]
      apply sSup_le
      rintro _ ⟨heap_remove, heap_remain, h_disjoint, h_union, rfl⟩
      rw [← unit_le_div_iff_mul_le]
      obtain ⟨q, h_q⟩ := qslSup_qslPointsTo_iff e_loc ⟨s.stack, heap_remove⟩
      rw [h_q]
      simp only [qslPointsTo, iteOneZero_le, forall_exists_index, and_imp]
      intro l' h_loc' h_val'
      simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_loc'
      rw [unit_le_div_iff_mul_le]
      simp only [one_mul]
      apply sInf_le_of_le
      · use (singleton l (e_val s.stack))
        apply And.intro
        · rw [h_loc'] at h_val'
          simp only
          rw [State.disjoint_comm] at h_disjoint
          apply disjoint_singleton_of_disjoint_alloc h_disjoint
          simp only [h_val', State.singleton, ↓reduceIte, ne_eq, not_false_eq_true]
        · rfl
      · simp only [qslPointsTo]
        rw [iteOneZero_pos]
        · rw [unit_div_one, ← h_union, h_val', ← substituteLoc_union, h_loc',
            substituteLoc_singleton_eq, union_comm]
          apply disjoint_singleton_of_disjoint_singleton
          rw [h_val', h_loc', disjoint_comm _ _] at h_disjoint
          exact h_disjoint
        · use l, h_loc.symm
    case neg h_ne_alloc =>
      apply sSup_le
      rintro _ ⟨heap_remove, heap_remain, _, h_union, rfl⟩
      rw [← unit_le_div_iff_mul_le]
      obtain ⟨q, h_q⟩ := qslSup_qslPointsTo_iff e_loc ⟨s.stack, heap_remove⟩
      rw [h_q]
      simp only [qslPointsTo, iteOneZero_le, forall_exists_index, and_imp]
      intro l h_loc h_val
      exfalso
      apply h_ne_alloc
      use l, h_loc.symm
      rw [← h_union, h_val]
      apply ne_undef_of_union_of_ne_undef
      simp only [State.singleton, ↓reduceIte, ne_eq, not_false_eq_true]


theorem wrlp_lookup :
    `[qsl| S (q : ℚ). e_loc ↦ q ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ q))
          ⊢ wrlp [ [Prog| v ≔* e_loc] ] ([[P]] | [[RI]])] := by
  sorry

end CQSL
