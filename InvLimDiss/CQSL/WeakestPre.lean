import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Quantitative
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Syntax Semantics QSL unitInterval

namespace CQSL

variable {Var : Type}

abbrev progState := (Program Var) × (State Var)

noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a, ∑' cs : progState, (programSmallStepSemantics c s a cs.1 cs.2) * inner cs.1 cs.2 = x}

theorem skip_support_finite (s : State Var) (inner : Program Var → StateRV Var):
    Set.Finite { cs : progState | programSmallStepSemantics [Prog| skip] s Action.deterministic cs.1 cs.2 * inner cs.1 cs.2 ≠ 0} := by
  apply Set.Finite.subset
  · have : Set.Finite ({⟨[Prog| ↓], s⟩} : Set progState) := Set.finite_singleton _
    exact this
  · intro cs h_cs
    unfold programSmallStepSemantics skipSmallStepSemantics iteOneZero ite_unit at h_cs
    simp only [true_and, ite_mul, one_mul, zero_mul, ne_eq, ite_eq_right_iff, and_imp,
      Classical.not_imp, Set.mem_setOf_eq] at h_cs
    obtain ⟨h_c, h_s, _⟩ := h_cs
    simp only [Set.mem_singleton_iff]
    rw [Prod.mk.inj_iff]
    use h_c, h_s.symm

theorem tsum_of_skip (c : Program Var) (inner : Program Var → StateRV Var) (s : State Var) :
    (∑' cs : progState,
    (programSmallStepSemantics [Prog| skip] s Action.deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] s := by
  rw [tsum_eq_finsum (skip_support_finite s inner)]
  sorry



end CQSL
