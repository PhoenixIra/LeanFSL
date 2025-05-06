import LeanFSL.SL.FuzzyProofrules
import LeanFSL.SL.Classical
import LeanFSL.Program.Semantics
import LeanFSL.Program.Expressions

/-! Framing is the act of removing a part of the separation logic objects out of the entailment.
  In its trivial case, we can just use the monotonicity of the operation.
  However, when we also want to move it along a program semantics object, we require
  certain additional criteria on the program and the formula.
  We formulate these requirements here:
  * `wrtProg` are the program variables on the left side of assignments
  * `varRV` are the program variables occuring in a random variable-/

open Semantics FSL State

namespace Syntax

variable {Var : Type}

/-- Variables on the left of assignments in this statement -/
def wrtStmt : Program Var → Set Var
  | [Prog| ↓] => ∅
  | [Prog| ↯] => ∅
  | [Prog| skip] => ∅
  | [Prog| v ≔ _] => {v}
  | [Prog| _ *≔ _] => ∅
  | [Prog| v ≔* _] => {v}
  | [Prog| v ≔ cas(_, _, _)] => {v}
  | [Prog| v ≔ alloc(_)] => {v}
  | [Prog| free(_, _)] => ∅
  | [Prog| if _ then [[_]] else [[_]] fi] => ∅
  | [Prog| pif _ then [[_]] else [[_]] fi] => ∅
  | [Prog| [[c₁]] ; [[_]]] => wrtStmt c₁
  | [Prog| while _ begin [[_]] fi] => ∅
  | [Prog| [[c₁]] || [[c₂]]] => wrtStmt c₁ ∪ wrtStmt c₂

/-- Variables on the left of assignments in the program -/
def wrtProg : Program Var → Set Var
  | [Prog| ↓] => ∅
  | [Prog| ↯] => ∅
  | [Prog| skip] => ∅
  | [Prog| v ≔ _] => {v}
  | [Prog| _ *≔ _] => ∅
  | [Prog| v ≔* _] => {v}
  | [Prog| v ≔ cas(_, _, _)] => {v}
  | [Prog| v ≔ alloc(_)] => {v}
  | [Prog| free(_, _)] => ∅
  | [Prog| if _ then [[c₁]] else [[c₂]] fi] => wrtProg c₁ ∪ wrtProg c₂
  | [Prog| pif _ then [[c₁]] else [[c₂]] fi] => wrtProg c₁ ∪ wrtProg c₂
  | [Prog| [[c₁]] ; [[c₂]]] => wrtProg c₁ ∪ wrtProg c₂
  | [Prog| while _ begin [[c]] fi] => wrtProg c
  | [Prog| [[c₁]] || [[c₂]]] => wrtProg c₁ ∪ wrtProg c₂

-- def varValueExp (e : ValueExp Var) : Set Var := { v | ∃ s q, e s ≠ e (substituteVar s v q)}
-- def varProbExp (e : ProbExp Var) : Set Var := { v | ∃ s q, e s ≠ e (substituteVar s v q)}
-- def varBoolExp (e : BoolExp Var) : Set Var := { v | ∃ s q, e s ≠ e (substituteVar s v q)}

def varStmt : Program Var → Set Var
  | [Prog| ↓] => ∅
  | [Prog| ↯] => ∅
  | [Prog| skip] => ∅
  | [Prog| v ≔ e] => {v} ∪ varValue e
  | [Prog| e *≔ e'] => varValue e ∪ varValue e'
  | [Prog| v ≔* e] => {v} ∪ varValue e
  | [Prog| v ≔ cas(e,e',e'')] => {v} ∪ varValue e ∪ varValue e' ∪ varValue e''
  | [Prog| v ≔ alloc(e)] => {v} ∪ varValue e
  | [Prog| free(e,e')] => varValue e ∪ varValue e'
  | [Prog| if e then [[_]] else [[_]] fi] => varBool e
  | [Prog| pif e then [[_]] else [[_]] fi] => varProb e
  | [Prog| [[c]] ; [[_]]] => varStmt c
  | [Prog| while e begin [[_]] fi] => varBool e
  | [Prog| [[c₁]] || [[c₂]]] => varStmt c₁ ∪ varStmt c₂

def varProg : Program Var → Set Var
  | [Prog| ↓] => ∅
  | [Prog| ↯] => ∅
  | [Prog| skip] => ∅
  | [Prog| v ≔ e] => {v} ∪ varValue e
  | [Prog| e *≔ e'] => varValue e ∪ varValue e'
  | [Prog| v ≔* e] => {v} ∪ varValue e
  | [Prog| v ≔ cas(e,e',e'')] => {v} ∪ varValue e ∪ varValue e' ∪ varValue e''
  | [Prog| v ≔ alloc(e)] => {v} ∪ varValue e
  | [Prog| free(e,e')] => varValue e ∪ varValue e'
  | [Prog| if e then [[c₁]] else [[c₂]] fi] => varBool e ∪ varProg c₁ ∪ varProg c₂
  | [Prog| pif e then [[c₁]] else [[c₂]] fi] => varProb e ∪ varProg c₁ ∪ varProg c₂
  | [Prog| [[c₁]] ; [[c₂]]] => varProg c₁ ∪ varProg c₂
  | [Prog| while e begin [[c]] fi] => varBool e ∪ varProg c
  | [Prog| [[c₁]] || [[c₂]]] => varProg c₁ ∪ varProg c₂

end Syntax

namespace FSL

/-- Variables occuring in an expression, semantically defined. I.e. variables that never change
  the outcome of `f`. -/
def varRV (f : StateRV Var) : Set Var := { v | ∃ s q, f s ≠ f (s.substituteStack v q)}

open SL in
def varProp (P : StateProp Var) : Set Var := {v | ∃ s q, P s ≠ P (s.substituteStack v q)}

end FSL
