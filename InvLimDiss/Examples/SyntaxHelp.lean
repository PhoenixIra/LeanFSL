import InvLimDiss.Program
import InvLimDiss.Mathlib.Probabilities

open Syntax

def var (var : String) : ValueExp String :=
  λ s => s var

def const (val : ℚ) : ValueExp String :=
  λ _ => val

def add (l r : ValueExp String) : ValueExp String :=
  λ s => l s + r s

def sub (l r : ValueExp String) : ValueExp String :=
  λ s => l s - r s

def dec (l : ValueExp String) : ValueExp String :=
  λ s => l s - 1

def inc (l : ValueExp String) : ValueExp String :=
  λ s => l s + 1

noncomputable def exp (l : ProbExp String) (r : ValueExp String) : ProbExp String :=
  λ s => if h : 0 ≤ (r s : ℝ) then unitInterval.rpow (l s) (⟨(r s), h⟩ : NNReal) else 1

def eq (l r : ValueExp String) : BoolExp String :=
  λ s => l s = r s

def leq (l r : ValueExp String) : BoolExp String :=
  λ s => l s ≤ r s

def lt (l r : ValueExp String) : BoolExp String :=
  λ s => l s < r s

noncomputable def half : ProbExp String := fun _ =>
  ⟨1/2, unitInterval.div_mem zero_le_one zero_le_two one_le_two⟩

noncomputable def one : ProbExp String := fun _ => 1

noncomputable def constP (p : unitInterval) : ProbExp String := fun _ => p

theorem inc_dec_ident : inc (dec e) = e := by
  funext s
  simp only [inc, dec, sub_add_cancel]

theorem dec_inc_ident : dec (inc e) = e := by
  funext s
  simp only [dec, inc, add_sub_cancel_right]

theorem substVal_of_var_neq (h : v ≠ v') : substVal (var v) v' e = var v := by
  unfold substVal
  funext s
  unfold var
  unfold State.substituteVar
  rw [if_neg h.symm]

theorem substVal_of_var : substVal (var v) v e = e := by
  unfold substVal
  funext s
  unfold var
  unfold State.substituteVar
  rw [if_pos rfl]

theorem substBool_of_leq : substBool (leq l r) v e = leq (substVal l v e) (substVal r v e) := rfl

theorem substBool_of_lt : substBool (lt l r) v e = lt (substVal l v e) (substVal r v e) := rfl

theorem substVal_of_const : substVal (const q) v e = const q := rfl

theorem substVal_of_dec : substVal (dec e) v e' = dec (substVal e v e') := rfl

theorem substVal_of_inc : substVal (inc e) v e' = inc (substVal e v e') := rfl

theorem substVal_of_sub :
    substVal (sub e e') v e'' = sub (substVal e v e'') (substVal e' v e'') := rfl

theorem substVal_of_add :
    substVal (add e e') v e'' = add (substVal e v e'') (substVal e' v e'') := rfl

theorem substProp_of_exp :
    substProb (exp e e') v e'' = exp (substProb e v e'') (substVal e' v e'') := rfl

theorem substProp_of_constP :
    substProb (constP p) v e' = constP p := rfl

theorem substProp_of_half :
    substProb half v e' = half := rfl

theorem varValue_of_var : varValue (var v) = {v} := by
  unfold varValue
  apply Set.Subset.antisymm
  · rintro t ⟨s, q, h⟩
    simp only [Set.mem_singleton_iff]
    unfold var at h
    unfold State.substituteVar at h
    split_ifs at h
    case pos h_eq => exact h_eq
    case neg h_ne => exfalso; exact h rfl
  · simp only [ne_eq, Set.singleton_subset_iff, Set.mem_setOf_eq]
    use (fun _ => 0), 1
    simp only [var, State.substituteVar, ↓reduceIte, one_ne_zero, not_false_eq_true]

theorem varValue_of_const : varValue (const r) = ∅ := by
  unfold varValue
  apply Set.Subset.antisymm
  · rintro t ⟨s, q, h⟩
    exfalso
    unfold const at h
    exact h rfl
  · simp only [ne_eq, Set.empty_subset]

theorem varValue_of_add : varValue (add l r) ⊆ varValue l ∪ varValue r := by
  simp only [ne_eq, varValue]
  intro a ⟨s, q, h⟩
  simp only [add] at h
  cases eq_or_ne (l (State.substituteVar s a q)) (l s)
  case inl h_l =>
    right
    use s, q
    intro h_r
    simp only [h_l, h_r, not_true_eq_false] at h
  case inr h_l =>
    left
    use s, q

theorem varValue_of_dec : varValue (dec e) = varValue e := by
  apply Set.Subset.antisymm
  · simp only [varValue, ne_eq]
    intro a ⟨s, q, h⟩
    simp only [dec, sub_left_inj] at h
    use s, q
  · simp only [varValue, ne_eq, Set.setOf_subset_setOf, forall_exists_index]
    intro a s q h
    use s, q
    simp only [dec, sub_left_inj, h, not_false_eq_true]

theorem varValue_of_inc : varValue (inc e) = varValue e := by
  apply Set.Subset.antisymm
  · simp only [varValue, ne_eq]
    intro a ⟨s, q, h⟩
    simp only [inc, add_left_inj] at h
    use s, q
  · simp only [varValue, ne_eq, Set.setOf_subset_setOf, forall_exists_index]
    intro a s q h
    use s, q
    simp only [inc, add_left_inj, h, not_false_eq_true]

theorem varProb_of_one : varProb one = ∅ := by
  unfold varProb
  apply Set.Subset.antisymm
  · rintro r ⟨s, q, h⟩
    exfalso
    unfold one at h
    exact h rfl
  · exact Set.empty_subset _

theorem varProb_of_half : varProb half = ∅ := by
  unfold varProb
  apply Set.Subset.antisymm
  · rintro r ⟨s, q, h⟩
    exfalso
    unfold half at h
    exact h rfl
  · exact Set.empty_subset _

theorem varProb_of_constP : varProb (constP p) = ∅ := by
  unfold varProb
  apply Set.Subset.antisymm
  · rintro r ⟨s, q, h⟩
    exfalso
    unfold constP at h
    exact h rfl
  · exact Set.empty_subset _

theorem varProb_of_exp : varProb (exp e e') ⊆ varProb e ∪ varValue e' := by
  unfold varProb varValue
  rintro r ⟨s, q, h⟩
  simp only [ne_eq, Set.mem_union, Set.mem_setOf_eq]
  by_cases h' : e (State.substituteVar s r q) = e s
  case neg => left; use s, q
  case pos =>
    right
    use s, q
    intro h''
    apply h
    unfold exp
    rw [h', h'']


theorem varBool_of_leq : varBool (leq l r) ⊆ varValue l ∪ varValue r := by
  simp only [varBool, ne_eq, varValue]
  intro a ⟨s, q, h⟩
  simp only [leq, decide_eq_decide] at h
  cases eq_or_ne (l (State.substituteVar s a q)) (l s)
  case inl h_l =>
    right
    use s, q
    intro h_r
    simp only [h_l, h_r, not_true_eq_false] at h
  case inr h_l =>
    left
    use s, q

theorem varBool_of_eq : varBool (eq l r) ⊆ varValue l ∪ varValue r := by
  simp only [varBool, ne_eq, varValue]
  intro a ⟨s, q, h⟩
  simp only [eq, decide_eq_decide] at h
  cases eq_or_ne (l (State.substituteVar s a q)) (l s)
  case inl h_l =>
    right
    use s, q
    intro h_r
    simp only [h_l, h_r, not_true_eq_false] at h
  case inr h_l =>
    left
    use s, q


theorem half_le_one : half s ≤ one s := by
  simp only [one]
  open unitInterval in
  exact le_one'

theorem leq_le_leq_succ (n : ℕ) (e : ValueExp String) :
    leq (const (↑n + 1)) e s → leq (const ↑n) e s := by
  simp only [leq, const, decide_eq_true_eq]
  intro h
  apply le_trans ?_ h
  simp only [le_add_iff_nonneg_right, zero_le_one]
