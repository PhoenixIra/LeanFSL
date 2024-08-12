import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Framing.Basic

/-! Simplication lemmas for substitution. -/


namespace QSL

open Syntax QSL State

@[simp]
theorem qslSubst_of_qslTrue : `[qsl| qTrue(v ↦ e)] = `[qsl| qTrue] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslFalse : `[qsl| qFalse(v ↦ e)] = `[qsl| qFalse] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslEmp : `[qsl| emp(v ↦ e)] = `[qsl| emp] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslPointsTo : `[qsl| e' ↦ e''(v ↦ e)] = `[qsl| (substVal e' v e) ↦ (substVal e'' v e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslEquals : `[qsl| e' = e''(v ↦ e)] = `[qsl| (substVal e' v e) = (substVal e'' v e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslReal : `[qsl| <r>(v ↦ e)] = `[qsl| <substProb r v e>] := by
  apply funext
  intro s
  rfl

noncomputable def substProp (P : State Var → Prop) (v : Var) (e : ValueExp Var) : State Var → Prop :=
  fun s => P (s.substituteStack v (e s.stack))

@[simp]
theorem qslSubst_of_qslIverson : `[qsl| ⁅b⁆(v ↦ e)] = `[qsl| ⁅substProp b v e⁆] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslNot : `[qsl| (~[[f]])(v ↦ e)] = `[qsl| ~([[f]](v ↦ e))] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslMin : `[qsl| ([[f]] ⊓ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⊓ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslMax : `[qsl| ([[f]] ⊔ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⊔ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslAdd : `[qsl| ([[f]] + [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) + [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslMul : `[qsl| ([[f]] ⬝ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⬝ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslSup {f : α → StateRV Var} :
    `[qsl| (S (a : α). [[f a]] )(v ↦ e)] = `[qsl| S (a : α). [[(f a)]](v ↦ e)] := by
  apply funext
  intro s
  simp only [qslSubst, qslSup]
  apply le_antisymm
  · apply sSup_le_sSup
    simp only [Set.range, Subtype.exists, exists_prop, Set.setOf_subset_setOf, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    rintro _ ⟨x, rfl⟩
    use (qslSubst (f x) v e)
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
theorem qslSubst_of_qslInf {f : α → StateRV Var} :
    `[qsl| (I (a : α). [[f a]] )(v ↦ e)] = `[qsl| I (a : α). [[(f a)]](v ↦ e)] := by
  apply funext
  intro s
  simp only [qslSubst, qslSup]
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
    use (qslSubst (f x) v e)
    apply And.intro
    · use x
    · rfl

@[simp]
theorem qslSubst_of_qslSepMul :
    `[qsl| ([[f]] ⋆ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⋆ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

@[simp]
theorem qslSubst_of_qslSepDiv :
    `[qsl| ([[f]] -⋆ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) -⋆ [[g]](v ↦ e)] := by
  apply funext
  intro s
  rfl

theorem substituteStack_of_qslSepCon (e : ValueExp Var) (h : v ∉ varRV g) :
    `[qsl| ([[f]] ⋆ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⋆ [[g]]] := by
  rw [qslSubst_of_qslSepMul]
  rw [qslSubst_eq_of_not_varRV h e]

end QSL
