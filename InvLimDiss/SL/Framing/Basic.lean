import InvLimDiss.SL.Framing.Defs


open Syntax Semantics QSL State

namespace QSL


theorem substituteStack_eq_of_not_varStateRV {f : StateRV Var} {v : Var} (h : v ∉ varStateRV f) :
    ∀ q s, f (s.substituteStack v q) = f s := by
  intro q s
  simp only [varStateRV, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h
  exact (h s q).symm

theorem substituteVar_eq_of_not_varStateRV {f : StateRV Var} {v : Var} (h : v ∉ varStateRV f) :
    ∀ q stack heap, f ⟨substituteVar stack v q, heap⟩ = f ⟨stack, heap⟩ := by
  intro q stack heap
  have := substituteStack_eq_of_not_varStateRV h q ⟨stack, heap⟩
  simp only [substituteStack] at this
  rw [this]

theorem qslSubst_eq_of_not_varStateRV {f : StateRV Var} {v : Var} (h : v ∉ varStateRV f) :
    ∀ e, `[qsl| [[f]](v ↦ e)] = f := by
  intro e
  apply funext
  intro s
  rw [qslSubst]
  exact substituteStack_eq_of_not_varStateRV h (e s.stack) s

end QSL
