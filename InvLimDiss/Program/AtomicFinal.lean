import InvLimDiss.Program.Semantics

namespace Atom

open Syntax Semantics unitInterval

variable {Var : Type}

def atomicProgram : Program Var → Bool
  | [Prog| skip] => true
  | [Prog| _ ≔ _] => true
  | [Prog| _ *≔ _] => true
  | [Prog| _ ≔* _] => true
  | [Prog| _ ≔ cas(_, _, _)] => true
  | [Prog| _ ≔ alloc(_)] => true
  | [Prog| free(_, _)] => true
  | _ => false

def finalProgram : Program Var → Bool
  | [Prog| ↓] => true
  | [Prog| ↯] => true
  | _ => false

theorem atomic_not_final {c : Program Var} (h : atomicProgram c) : ¬ finalProgram c := by
  rw [finalProgram]
  intro h_f
  split at h_f
  case h_1 => simp only [atomicProgram, Bool.false_eq_true] at h
  case h_2 => simp only [atomicProgram, Bool.false_eq_true] at h
  case h_3 h_n_term h_n_err => cases h_f

theorem finalPrograms_iff_or {c : Program Var} :
    finalProgram c ↔ c = [Prog| ↓] ∨ c = [Prog| ↯] := by
  apply Iff.intro
  · intro h
    rw [finalProgram] at h
    split at h
    case h_1 => exact Or.inl rfl
    case h_2 => exact Or.inr rfl
    case h_3 => cases h
  · intro h
    rw [finalProgram]
    split
    case h_1 => rfl
    case h_2 => rfl
    case h_3 h_n_term h_n_err => exfalso; cases h with
      | inl h => exact h_n_term h
      | inr h => exact h_n_err h

theorem semantics_eq_zero_of_atomProgram {c c' : Program Var}
    (h_atom : atomicProgram c) (h_c' : ¬ finalProgram c')
    (s : State Var) (a : Action) (s' : State Var) :
    programSmallStepSemantics c s a c' s' = 0 := by
  rw [finalPrograms_iff_or, not_or] at h_c'
  obtain ⟨h_n_term, h_n_err⟩ := h_c'
  rw [atomicProgram] at h_atom
  split at h_atom
  case h_1 =>
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_zero_def]
    rintro ⟨h_term, _⟩
    exact h_n_term h_term
  case h_2 =>
    simp only [programSmallStepSemantics, assignSmallStepSemantics]
  case h_3 =>
    simp only [programSmallStepSemantics, manipulateSmallStepSemantics]
  case h_4 =>
    simp only [programSmallStepSemantics, lookupSmallStepSemantics]
  case h_5 =>
    simp only [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  case h_6 =>
    simp only [programSmallStepSemantics, allocateSmallStepSemantics]
  case h_7 =>
    simp only [programSmallStepSemantics, freeSmallStepSemantics]
  case h_8 =>
    cases h_atom

end Atom
