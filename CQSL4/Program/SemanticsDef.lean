import CQSL4.Program.Semantics


namespace Semantics

open unitInterval Syntax Program State Classical

variable {Variable : Type}

/- error statement lemmas -/

theorem error_def (s s' : State Variable) (c : Program Variable) (a : Action) :
    programSmallStepSemantics error s a c s' = 0 := by
  apply zero_probability_of_not_enabledAction
  simp only [enabledAction, Set.mem_empty_iff_false, not_false_eq_true]


/- terminated statement lemmas -/

theorem terminated_def (s s' : State Variable) (c : Program Variable) (a : Action) :
    programSmallStepSemantics terminated s a c s' = 0 := by
  apply zero_probability_of_not_enabledAction
  simp only [enabledAction, Set.mem_empty_iff_false, not_false_eq_true]


/- skip statement lemmas -/

theorem skip_zero (s s' : State Variable) (c : Program Variable) {a : Action} (h : a ≠ Action.deterministic) :
    programSmallStepSemantics skip s a c s' = 0 := by
  apply zero_probability_of_not_enabledAction
  simp only [enabledAction, Set.mem_singleton_iff]
  exact h

theorem skip_one (s : State Variable) :
    programSmallStepSemantics skip s Action.deterministic terminated s = 1 := by
  simp only [programSmallStepSemantics, skipSmallStepSemantics, true_and, ite_one_zero_pos]


/- value assignment statement lemmas -/

theorem valAssign_zero_of_not_action (s s' : State Variable) (v : Variable) {e : ValueExp Variable}
    (c : Program Variable) {a : Action} (h : a ≠ Action.deterministic) :
    programSmallStepSemantics (valAssign v e) s a c s' = 0 := by
  apply zero_probability_of_not_enabledAction
  simp only [enabledAction, Set.mem_singleton_iff]
  exact h

theorem valAssign_zero_of_not_defined_expr (s s' : State Variable) (v : Variable) {e : ValueExp Variable}
    {a : Action} (h : e s.stack = none) :
    programSmallStepSemantics (valAssign v e) s a terminated s' = 0 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics]
  rw [ite_one_zero_neg]; simp only [ne_eq, not_and, not_exists]; intro _ _ h_x; rw [h_x] at h; exfalso; cases h

theorem valAssign_one_of_not_defined_expr {s : State Variable} (v : Variable) {e : ValueExp Variable}
    (h : e s.stack = none) :
    programSmallStepSemantics (valAssign v e) s Action.deterministic error s = 1 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics, true_and]
  rw [ite_one_zero_pos]
  exact Or.inl h

theorem valAssign_zero_of_not_defined_var (s s' : State Variable) (v : Variable) {e : ValueExp Variable}
    {a : Action} (h : s.stack v = none) :
    programSmallStepSemantics (valAssign v e) s a terminated s' = 0 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics]
  rw [ite_one_zero_neg]; simp only [ne_eq, not_and, not_exists]; intro _ _ _ h_s; exfalso; cases h_s h

theorem valAssign_one_of_not_defined_var {s : State Variable} (v : Variable) {e : ValueExp Variable}
    (h : s.stack v = none) :
    programSmallStepSemantics (valAssign v e) s Action.deterministic error s = 1 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics, true_and]
  rw [ite_one_zero_pos]
  exact Or.inr h

theorem valAssign_zero_of_not_substitute {s s' : State Variable} {v : Variable} {e : ValueExp Variable}
    {q : ℚ} (h_q : e s.stack = some q) (h_s : substituteStack s v q ≠ s') :
    programSmallStepSemantics (valAssign v e) s Action.deterministic terminated s' = 0 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics, ne_eq, true_and]
  rw [ite_one_zero_neg]
  simp only [not_exists, not_and]
  intro x h_x h_v
  rw [h_x] at h_q
  cases h_q
  exact h_s

theorem valAssign_one {s s' : State Variable} (v : Variable) {e : ValueExp Variable}
    {q : ℚ} (h_q : e s.stack = some q) (h_v : s.stack v ≠ none) (h_s : substituteStack s v q = s') :
    programSmallStepSemantics (valAssign v e) s Action.deterministic terminated s' = 1 := by
  simp only [programSmallStepSemantics, valAssignSmallStepSemantics, ne_eq, true_and]
  rw [ite_one_zero_pos]
  use q


/- manipulate heap statement lemmas -/

theorem manipulate_zero_of_not_action (s s' : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (c : Program Variable) {a : Action} (h : a ≠ Action.deterministic) :
    programSmallStepSemantics (manipulate v e) s a c s' = 0 := by
  apply zero_probability_of_not_enabledAction
  simp only [enabledAction, Set.mem_singleton_iff]
  exact h

theorem manipulate_zero_of_undefined_location (s s' : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (a : Action) (h : e_loc s.stack = none) :
    programSmallStepSemantics (manipulate e_loc e_val) s a terminated s' = 0 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_neg]
  simp only [not_and, not_exists]
  intro _ l h_l
  rw [h] at h_l; cases h_l

theorem manipulate_zero_of_undefined_value (s s' : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (a : Action) (h : e_val s.stack = none) :
    programSmallStepSemantics (manipulate e_loc e_val) s a terminated s' = 0 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_neg]
  simp only [not_and, not_exists]
  intro _ _ _ _ q h_q
  rw [h] at h_q; cases h_q

theorem manipulate_zero_of_not_alloc (s s' : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (a : Action) {l : ℕ} (h_l : e_loc s.stack = some l) (h_notAlloc : s.heap l = none):
    programSmallStepSemantics (manipulate e_loc e_val) s a terminated s' = 0 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_neg]
  simp only [not_and, not_exists]
  intro _ l' h_l' h_alloc
  rw [h_l'] at h_l
  cases h_l; exfalso
  exact h_alloc h_notAlloc

theorem manipulate_zero_of_not_substitute {s s' : State Variable} {e_loc : LocationExp Variable} {e_val : ValueExp Variable}
    {l : ℕ} {q : ℚ} (h_l : e_loc s.stack = some l) (h_q : e_val s.stack = some q) (h_change : substituteHeap s l q ≠ s') :
    programSmallStepSemantics (manipulate e_loc e_val) s Action.deterministic terminated s' = 0 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_neg]
  simp only [not_and, not_exists]
  intro _ l' h_l' h_alloc q' h_q'
  rw [h_l'] at h_l; rw [h_q'] at h_q
  cases h_l; cases h_q
  exact h_change

theorem manipulate_one_of_undefined_location (s : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (h : e_loc s.stack = none) :
    programSmallStepSemantics (manipulate e_loc e_val) s Action.deterministic error s = 1 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_pos]
  simp only [true_and]
  exact Or.inl h

theorem manipulate_one_of_undefined_value(s : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    (h : e_val s.stack = none) :
    programSmallStepSemantics (manipulate e_loc e_val) s Action.deterministic error s = 1 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_pos]
  simp only [true_and]
  exact Or.inr <| Or.inr h

theorem manipulate_one_of_not_alloc (s : State Variable) (e_loc : LocationExp Variable) (e_val : ValueExp Variable)
    {l : ℕ} (h_l : e_loc s.stack = some l) (h_notAlloc : s.heap l = none):
    programSmallStepSemantics (manipulate e_loc e_val) s Action.deterministic error s = 1 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq]
  rw [ite_one_zero_pos]
  simp only [true_and]
  apply Or.inr; apply Or.inl
  use l

theorem manipulate_one {s s' : State Variable} {e_loc : LocationExp Variable} {e_val : ValueExp Variable}
    {l : ℕ} {q : ℚ} (h_l : e_loc s.stack = some l) (h_q : e_val s.stack = some q) (h_alloc : s.heap l ≠ none) (h_change : substituteHeap s l q = s') :
    programSmallStepSemantics (manipulate e_loc e_val) s Action.deterministic terminated s' = 1 := by
  simp only [programSmallStepSemantics, manipulateSmallStepSemantics, ne_eq, true_and]
  rw [ite_one_zero_pos]
  exact ⟨l, h_l, h_alloc, ⟨q, h_q, h_change⟩⟩
