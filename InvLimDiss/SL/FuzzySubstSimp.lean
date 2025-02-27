import InvLimDiss.SL.FuzzyProofrules
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Framing.Basic

/-! Simplication lemmas for substitution. -/


namespace FSL

open Syntax FSL State

@[simp]
theorem fslSubst_of_fslTrue : `[fsl| fTrue(v ↦ e)] = `[fsl| fTrue] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslFalse : `[fsl| fFalse(v ↦ e)] = `[fsl| fFalse] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslEmp : `[fsl| emp(v ↦ e)] = `[fsl| emp] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslPointsTo : `[fsl| e' ↦ e''(v ↦ e)] = `[fsl| (substVal e' v e) ↦ (substVal e'' v e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslEquals : `[fsl| e' === e''(v ↦ e)]
    = `[fsl| (substVal e' v e) === (substVal e'' v e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslReal : `[fsl| <r>(v ↦ e)] = `[fsl| <substProb r v e>] := by
  apply funext
  intro s
  rfl

-- noncomputable def substProp (P : State Var → Prop) (v : Var) (e : ValueExp Var) : State Var → Prop :=
--   fun s => P (s.substituteStack v (e s.stack))

-- @[simp]
-- theorem fslSubst_of_fslIverson : `[fsl| ⁅b⁆(v ↦ e)] = `[fsl| ⁅substProp b v e⁆] := by
--   apply funext
--   intro s
--   rfl

@[simp]
theorem fslSubst_of_fslNot : `[fsl| (~[[f]])(v ↦ e)] = `[fsl| ~([[f]](v ↦ e))] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslMin : `[fsl| ([[f]] ⊓ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) ⊓ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslMax : `[fsl| ([[f]] ⊔ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) ⊔ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslAdd : `[fsl| ([[f]] + [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) + [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslMul : `[fsl| ([[f]] ⬝ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) ⬝ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslSup {f : α → StateRV Var} :
    `[fsl| (S (a : α). [[f a]] )(v ↦ e)] = `[fsl| S (a : α). [[(f a)]](v ↦ e)] := by
  apply funext
  intro s
  simp only [fslSubst, fslSup]
  apply le_antisymm
  · apply sSup_le_sSup
    simp only [Set.range, Subtype.exists, exists_prop, Set.setOf_subset_setOf, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x, rfl⟩
    use (fslSubst (f x) v e)
    apply And.intro
    · use x
    · rfl
  · apply sSup_le_sSup
    simp only [Set.range, Subtype.exists, exists_prop, Set.setOf_subset_setOf, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x, rfl⟩
    use (f x)
    apply And.intro
    · use x
    · rfl

@[simp]
theorem fslSubst_of_fslInf {f : α → StateRV Var} :
    `[fsl| (I (a : α). [[f a]] )(v ↦ e)] = `[fsl| I (a : α). [[(f a)]](v ↦ e)] := by
  apply funext
  intro s
  simp only [fslSubst, fslSup]
  apply le_antisymm
  · apply sInf_le_sInf
    simp only [Set.range, Subtype.exists, exists_prop, Set.setOf_subset_setOf, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x, rfl⟩
    use (f x)
    apply And.intro
    · use x
    · rfl
  · apply sInf_le_sInf
    simp only [Set.range, Subtype.exists, exists_prop, Set.setOf_subset_setOf, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x, rfl⟩
    use (fslSubst (f x) v e)
    apply And.intro
    · use x
    · rfl

@[simp]
theorem fslSubst_of_fslSepMul :
    `[fsl| ([[f]] ⋆ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) ⋆ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem fslSubst_of_fslSepDiv :
    `[fsl| ([[f]] -⋆ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) -⋆ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

theorem fslSubst_of_fslBigSepMul {f : ℕ → StateRV Var} :
    `[fsl| ([⋆] i ∈ { ... n}. [[f i]])(v ↦ e) ]
    = `[fsl| [⋆] i ∈ { ... n}. [[f i]](v ↦ e) ] := by
  induction n with
  | zero => apply funext; intro s; rfl
  | succ n ih =>
    unfold fslBigSepMul
    rw [fslSubst_of_fslSepMul, ih]

theorem substituteStack_of_fslSepCon (e : ValueExp Var) (h : v ∉ varRV g) :
    `[fsl| ([[f]] ⋆ [[g]])(v ↦ e)] = `[fsl| [[f]](v ↦ e) ⋆ [[g]]] := by
  rw [fslSubst_of_fslSepMul]
  rw [fslSubst_eq_of_not_varRV h e]

end FSL
