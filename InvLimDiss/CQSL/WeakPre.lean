import InvLimDiss.CQSL.Step
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.AtomicFinal
import Mathlib.Order.FixedPoints


namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics

variable {Var : Type}

noncomputable def wrlp_step (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[qsl| qFalse]
  | X, program => `[qsl| [[resource]] -⋆ [[step program (fun c => `[qsl| [[X c]] ⋆ [[resource]] ]) ]] ]

theorem wrlp_monotone (post : StateRV Var) (resource : StateRV Var) : Monotone (wrlp_step post resource) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro c
  unfold wrlp_step
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply monotone_qslSepImp le_rfl
    apply monotone_step
    rw [Pi.le_def]
    intro c
    rw [Pi.le_def]
    intro s
    apply monotone_qslSepCon
    · rw [Pi.le_def] at h_X
      exact h_X c
    · exact le_rfl

noncomputable def wrlp' (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :=
  gfp ⟨wrlp_step post resource, wrlp_monotone post resource⟩ program

syntax "wrlp [" term "] (" qsl " | " qsl ")" : qsl
macro_rules
  | `(term| `[qsl| wrlp [$c:term] ($p:qsl | $r:qsl)]) => `(wrlp' $c `[qsl| $p] `[qsl| $r])
  | `(term| `[qsl $v| wrlp [$c:term] ($p:qsl | $r:qsl)]) => `(wrlp' $c `[qsl $v| $p] `[qsl $v| $r])

open Lean PrettyPrinter Delaborator

def makeBrackets [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander wrlp']
def unexpanderWrlp : Unexpander
  | `($_ $c:term $p $r) =>
      do `(`[qsl| wrlp [$c:term] ($(← makeBrackets p):qsl | $(← makeBrackets r):qsl )])
  | _ => throw ()


theorem wrlp_def (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrlp [program] ([[post]] | [[resource]])] = match program with
  | [Prog| ↓ ] => post
  | [Prog| ↯ ] => `[qsl| qFalse]
  | program => `[qsl| [[resource]] -⋆ [[step program
    (fun c => `[qsl| wrlp [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [wrlp', ← map_gfp, coe_mk, wrlp_step]
  split
  case h_1 =>
    split
    case h_1 => rfl
    case h_2 h => cases h
    case h_3 => rfl
  case h_2 =>
    split
    case h_1 h => cases h
    case h_2 => rfl
    case h_3 => rfl
  case h_3 h_n_term h_n_err =>
    split
    case h_1 => exfalso; apply h_n_term; rfl
    case h_2 => exfalso; apply h_n_err; rfl
    case h_3 => rfl

theorem wrlp_eq_of_not_final {program : Program Var} (h_not_final : ¬ finalProgram program)
    (post : StateRV Var) (resource : StateRV Var) : `[qsl| wrlp [program] ([[post]] | [[resource]])]
    = `[qsl| [[resource]] -⋆ [[step program
      (fun c => `[qsl| wrlp [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by
  rw [finalPrograms_iff_or, not_or] at h_not_final
  obtain ⟨h_n_term, h_n_err⟩ := h_not_final
  rw [wrlp_def]
  split
  case h_1 => simp only [not_true_eq_false] at h_n_term
  case h_2 => simp only [not_true_eq_false] at h_n_err
  case h_3 => rfl

theorem wrlp_eq_of_term
    (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrlp [ [Prog| ↓] ] ([[post]] | [[resource]])] = post := by
  rw [wrlp_def]

theorem wrlp_eq_of_error
    (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrlp [ [Prog| ↯] ] ([[post]] | [[resource]])] = `[qsl| qFalse] := by
  rw [wrlp_def]

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
  rw [wrlp_eq_of_not_final this, le_qslSepImp_iff_qslSepCon_le]
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

theorem wrlp_skip : `[qsl| [[P]] ⊢ wrlp [ [Prog| skip] ] ([[P]] | [[RI]])] := by
  rw [wrlp_def]
  split
  case h_1 h_eq => cases h_eq
  case h_2 h_eq => cases h_eq
  case h_3 _ _ =>
    rw [le_qslSepImp_iff_qslSepCon_le, inf_tsum_skip, wrlp_eq_of_term]



end CQSL
