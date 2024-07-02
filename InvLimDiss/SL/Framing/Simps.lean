import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Framing.Defs

/-! Simplication lemmas (not necessary with the simp attribute) for variables occuring
in programs and qsl objects and substitution of variables. -/

open Syntax Semantics QSL State

namespace QSL

theorem varStateRV_of_qslTrue : varStateRV `[qsl Var| qTrue] = ∅ := by
  rw [varStateRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varStateRV_of_qslFalse : varStateRV `[qsl Var| qFalse] = ∅ := by
  rw [varStateRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varStateRV_of_qslEmp : varStateRV `[qsl Var| emp] = ∅ := by
  rw [varStateRV]
  simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    Decidable.not_not]
  intro _ _ _; rfl

theorem varStateRV_of_qslPointsTo :
    varStateRV `[qsl Var| e ↦ e'] ⊆ (varsValue e) ∪ (varsValue e') := by
  simp only [varStateRV, ne_eq, varsValue]
  intro x ⟨s,q,h⟩
  simp only [Set.mem_union, Set.mem_setOf_eq]
  simp only [qslPointsTo] at h
  by_cases h' : ∃ s q, ¬e (substituteVar s x q) = e s
  case pos => exact Or.inl h'
  case neg =>
    apply Or.inr
    use s.stack, q
    simp only [not_exists, Decidable.not_not] at h'
    specialize h' s.stack q
    by_cases h_n : ∃ n : PNat, n = e s.stack ∧ s.heap n = e' s.stack
    case pos =>
      rw [Eq.comm, unitInterval.iteOneZero_eq_iteOneZero_iff, not_iff] at h
      obtain h := h.mpr h_n
      simp only [substituteStack_heap, not_exists, not_and] at h
      obtain ⟨n, h_n, h_heap⟩ := h_n
      rw [← h'] at h_n
      specialize h n h_n
      rw [h_heap, HeapValue.val.injEq] at h
      exact Ne.symm h
    case neg =>
      rw [unitInterval.iteOneZero_eq_iteOneZero_iff, not_iff] at h
      obtain ⟨n, h_n', h⟩ := h.mp h_n
      rw [substituteStack, h'] at h_n'
      rw [substituteStack_heap] at h
      simp only [not_exists, not_and] at h_n
      have := h_n n h_n'
      rw [h, HeapValue.val.injEq] at this
      exact this


theorem substituteStack_eq_of_not_varStateRV {f : StateRV Var} {v : Var} (h : v ∉ varStateRV f) :
    ∀ q s, f (s.substituteStack v q) = f s := by
  intro q s
  simp only [varStateRV, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h
  exact (h s q).symm

theorem qslSubst_eq_of_not_varStateRV {f : StateRV Var} {v : Var} (h : v ∉ varStateRV f) :
    ∀ e, `[qsl| [[f]](v ↦ e)] = f := by
  intro e
  apply funext
  intro s
  rw [qslSubst]
  exact substituteStack_eq_of_not_varStateRV h (e s.stack) s

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
theorem qslSubst_of_qslMul : `[qsl| ([[f]] · [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) · [[g]](v ↦ e)] := by
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

theorem substituteStack_of_qslSepCon (e : ValueExp Var) (h : v ∉ varStateRV g) :
    `[qsl| ([[f]] ⋆ [[g]])(v ↦ e)] = `[qsl| [[f]](v ↦ e) ⋆ [[g]]] := by
  rw [qslSubst_of_qslSepMul]
  rw [qslSubst_eq_of_not_varStateRV h e]



end QSL
