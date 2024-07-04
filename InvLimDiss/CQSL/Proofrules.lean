import InvLimDiss.CQSL.WeakPre
import InvLimDiss.SL.Framing.Simps

/-!
  Proofrules for wrlp as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics

private theorem support_wrlp_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : progState =>
      programSmallStepSemantics c s a cs.1 cs.2
      * (`[qsl| (wrlp [cs.1] ([[P]] ⋆ [[resource]] | emp )) ⋆ emp ] cs.2))
    ⊆ { cs : progState | cs.1 = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_qsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.1
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrlp_eq_of_error, qslSepMul_qslEmp_eq, qslFalse] at h_qsl
      simp only [not_true_eq_false] at h_qsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.2

private theorem support_wrlp'_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : progState =>
      programSmallStepSemantics c s a cs.1 cs.2
      * (`[qsl| (wrlp [cs.1] ([[P]] | [[resource]] )) ⋆ [[resource]] ] cs.2))
    ⊆ { cs : progState | cs.1 = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_qsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.1
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrlp_eq_of_error, qslSepDiv_comm, qslSepMul_qslFalse_eq, qslFalse] at h_qsl
      simp only [not_true_eq_false] at h_qsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.2

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
    cases eq_or_ne (programSmallStepSemantics c s a cs.1.1 cs.1.2) 0 with
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
    cases eq_or_ne (programSmallStepSemantics c s a cs.1.1 cs.1.2) 0 with
    | inl h_zero =>
      rw [h_zero]
      simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_nzero =>
      apply unit_mul_le_mul le_rfl
      have := cs.prop
      simp only [Set.mem_setOf_eq] at this
      rw [this, wrlp_eq_of_term, wrlp_eq_of_term, qslSepMul_qslEmp_eq]

theorem wrlp_frame : `[qsl| wrlp [c] ([[P]] | [[RI]]) ⋆ [[F]] ⊢ wrlp [c] ([[P]] ⋆ [[F]] | [[RI]])] := by
  unfold wrlp'
  sorry

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

theorem wrlp_manipulate :
    `[qsl| (S (q : ℚ). e ↦ q) ⋆ (e ↦ e' -⋆ [[P]])
          ⊢ wrlp [ [Prog| e *≔ e'] ] ([[P]] | [[RI]])] := by
  rw [wrlp_eq_of_not_final (by simp only [finalProgram, Bool.false_eq_true, not_false_eq_true])]
  rw [le_qslSepDiv_iff_qslSepMul_le]
  sorry


end CQSL
