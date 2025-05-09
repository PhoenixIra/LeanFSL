import LeanFSL.Program.State
import LeanFSL.Mathlib.Probabilities
import LeanFSL.Mathlib.Ennreal

/-!
This file contains definitions and lemmas about expressions in our programming language.
To ease the process, we do not consider one syntax but allow arbitrary
(even noncomputable) lean functions here.
-/

namespace Syntax

open State unitInterval

variable (Variable : Type)

/-- Value expressions, i.e. mappings to `ℚ`. -/
def ValueExp := (Stack Variable) → ℚ

instance : Coe ℚ (ValueExp Variable) where
  coe q := fun _ => q

/-- Substitution of values in the expression, which we leave unevaluated. -/
@[simp]
noncomputable def substVal {Var : Type}
    (e : ValueExp Var) (v : Var) (e' : ValueExp Var) : ValueExp Var :=
  fun s => e (substituteVar s v (e' s))

/-- Variables in the expression that do not matter (or do not occure)-/
@[simp]
noncomputable def varValue {Var : Type} (e : ValueExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

instance : Coe Var (ValueExp Var) where
  coe x := λ s => s x


/-- Boolean expressions, i.e. mappings to `Bool`. -/
def BoolExp := (Stack Variable) → Bool

instance : Coe Bool (BoolExp Variable) where
  coe b := fun _ => b

/-- Substitution of values in the expression, which we leave unevaluated. -/
@[simp]
noncomputable def substBool {Var : Type}
    (e : BoolExp Var) (v : Var) (e' : ValueExp Var) : BoolExp Var :=
  fun s => e (substituteVar s v (e' s))

/-- Variables in the expression that matter (or occure)-/
@[simp]
noncomputable def varBool {Var : Type} (e : BoolExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}


/-- Probabilistic expressions, i.e. mappings to `unitInterval`. -/
def ProbExp := (Stack Variable) → I

instance : Coe I (ProbExp Variable) where
  coe i := fun _ => i

/-- Substitution of values in the expression, which we leave unevaluated. -/
@[simp]
noncomputable def substProb {Var : Type}
    (e : ProbExp Var) (v : Var) (e' : ValueExp Var) : ProbExp Var :=
  fun s => e (substituteVar s v (e' s))

/-- Variables in the expression that matter (or occure)-/
@[simp]
noncomputable def varProb {Var : Type} (e : ProbExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

/-- Quantitative expressions, i.e. mappings to `ENNReal`. -/
def QuantExp := (Stack Variable) → ENNReal

instance : Coe ENNReal (QuantExp Var) where
  coe i := fun _ => i

instance : Coe NNRat NNReal where
  coe i := ⟨(i.val : ℝ), by {norm_cast; apply le_trans i.prop; rfl}⟩

instance : Coe NNRat (QuantExp Var) where
  coe r := fun _ => r

/-- Substitution of values in the expression, which we leave unevaluated. -/
@[simp]
noncomputable def substQuant {Var : Type}
    (e : QuantExp Var) (v : Var) (e' : ValueExp Var) : QuantExp Var :=
  fun s => e (substituteVar s v (e' s))

/-- Variables in the expression that matter (or occure)-/
@[simp]
noncomputable def varsQuant {Var : Type} (e : QuantExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

end Syntax
