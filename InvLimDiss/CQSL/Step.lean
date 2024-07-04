import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.Framing.Basic
import InvLimDiss.Program.Support
import InvLimDiss.Program.Enabled
import InvLimDiss.Analysis.Tsum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.Pointwise

/-! This file features the step function and lemmas about it:
  * `step` which computes the next possible steps in a program
  * Monotonicty and Elimination lemmas about `step`-/

open Syntax Semantics QSL unitInterval Action State HeapValue Classical

namespace CQSL

variable {Var : Type}

/-- We introduce the abbreviation `progState` for the tuple consisting of programs and states.-/
abbrev progState := (Program Var) × (State Var)

/-- We introduce the abbreviation `semantics` for the probability transition function. -/
noncomputable abbrev semantics := @programSmallStepSemantics Var

/-- One step in the probability transition function -- essentially the bellman-operator. -/
noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : progState, (semantics c s a cs.1 cs.2) * inner cs.1 cs.2 = x}

theorem monotone_step (c : Program Var) : Monotone (step c) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro s
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  have : ∑' cs : progState, (semantics c s a cs.1 cs.2) * X cs.1 cs.2 ∈
    { x | ∃ a ∈ enabledAction c s,
      ∑' cs : progState, (semantics c s a cs.1 cs.2) * X cs.1 cs.2 = x} := by {
        use a
      }
  apply sInf_le_of_le this
  · apply tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (semantics c s a cs.1 cs.2) 0 with
    | inl h_eq =>
      rw [h_eq, zero_mul, zero_mul]
    | inr h_ne =>
      rw [Subtype.mk_le_mk, Set.Icc.coe_mul, Set.Icc.coe_mul]
      rw[mul_le_mul_left]
      · rw [Pi.le_def] at h_X
        specialize h_X cs.1
        rw [Pi.le_def] at h_X
        exact h_X cs.2
      · apply lt_of_le_of_ne nonneg'
        apply Ne.symm
        exact h_ne

theorem step_terminated (inner : Program Var → StateRV Var) :
    step [Prog| ↓] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

theorem step_error (inner : Program Var → StateRV Var) :
    step [Prog| ↯] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

theorem tsum_skip_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| skip] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_skip_support_superset s
  · rw [tsum_singleton (⟨[Prog| ↓], s⟩ : progState)
      (fun cs : progState => semantics [Prog| skip] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics skipSmallStepSemantics iteOneZero ite_unit
    simp only [and_self, ↓reduceIte, one_mul]

theorem step_skip (inner : Program Var → StateRV Var) :
    step [Prog| skip] inner s = inner [Prog| ↓] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_skip_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_skip_of_deterministic s inner]

theorem tsum_assign_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ e] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack s v (e s.stack)) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_assign_support_superset s
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack s v (e s.stack))⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ e] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics assignSmallStepSemantics iteOneZero ite_unit
    simp only [and_self, ↓reduceIte, one_mul]

theorem step_assign (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| v ≔ e] inner s = inner [Prog| ↓] (substituteStack s v (e s.stack)) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_assign_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_assign_of_deterministic s inner]

theorem tsum_manipulate_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) :
    (∑' cs : progState,
    (semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteHeap s l (e_val s.stack)) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_manipulate_support_superset s h_l h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteHeap s l (e_val s.stack))⟩ : progState)
      (fun cs : progState => semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics manipulateSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l h_alloc rfl

theorem step_manipulate (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) :
    step [Prog| e_loc *≔ e_val] inner s = inner [Prog| ↓] (substituteHeap s l (e_val s.stack)) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_manipulate_of_deterministic s inner h_l h_alloc
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_manipulate_of_deterministic s inner h_l h_alloc]

theorem tsum_manipulate_of_deterministic_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (∑' cs : progState,
    (semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↯] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_manipulate_error_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↯], s⟩ : progState)
      (fun cs : progState => semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics manipulateSmallStepSemantics iteOneZero ite_unit
    simp only [not_exists, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_or, not_and,
      not_forall, Decidable.not_not, and_imp, forall_exists_index]
    intro h' l h_l
    exfalso
    exact h' l h_l (h l h_l)

theorem step_manipulate_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    step [Prog| e_loc *≔ e_val] inner s = inner [Prog| ↯] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_manipulate_of_deterministic_of_error s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_manipulate_of_deterministic_of_error s inner h]

theorem tsum_lookup_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} {value : ℚ} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = value) :
    (∑' cs : progState,
    (semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack s v value) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_lookup_support_superset s h_l h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack s v value)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics lookupSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l.symm value h_alloc rfl

theorem step_lookup (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} {value : ℚ} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = value) :
    step [Prog| v ≔* e_loc] inner s = inner [Prog| ↓] (substituteStack s v value) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_lookup_of_deterministic s inner h_l h_alloc
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_lookup_of_deterministic s inner h_l h_alloc]

theorem tsum_lookup_of_deterministic_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (∑' cs : progState,
    (semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↯] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_lookup_error_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↯], s⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics lookupSmallStepSemantics iteOneZero ite_unit
    simp only [not_exists, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_or, not_and,
      not_forall, Decidable.not_not, and_imp, forall_exists_index]
    intro h' l h_l
    exfalso
    exact h' l h_l (h l h_l)

theorem step_lookup_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    step [Prog| v ≔* e_loc] inner s = inner [Prog| ↯] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_lookup_of_deterministic_of_error s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_lookup_of_deterministic_of_error s inner h]

theorem tsum_cas_of_eq_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = e_cmp s.stack) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack (substituteHeap s l (e_val s.stack)) v 1) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_cas_of_eq_support_superset s h_l h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack (substituteHeap s l (e_val s.stack)) v 1)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics compareAndSetSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and,
      not_or]
    intro h
    exfalso
    obtain ⟨h, _⟩ := h l h_l.symm (e_cmp s.stack) h_alloc
    exact h rfl rfl

theorem step_cas_of_eq (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = e_cmp s.stack) :
    step [Prog| v ≔ cas(e_loc, e_cmp, e_val)] inner s
    = inner [Prog| ↓] (substituteStack (substituteHeap s l (e_val s.stack)) v 1) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_cas_of_eq_of_deterministic s inner h_l h_alloc
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_cas_of_eq_of_deterministic s inner h_l h_alloc]

theorem tsum_cas_of_neq_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) (h_ne : s.heap l ≠ e_cmp s.stack) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack s v 0) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_cas_of_neq_support_superset s h_l h_alloc h_ne
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack s v 0)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics compareAndSetSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and,
      not_or]
    intro h
    exfalso
    specialize h l h_l.symm (getVal s.heap l h_alloc) (getVal_eq_self h_alloc rfl).symm
    rw [← val.injEq, getVal_eq_self h_alloc rfl] at h
    obtain ⟨_,h⟩ := h
    apply h
    · exact h_ne
    · exact True.intro

theorem step_cas_of_neq (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) (h_ne : s.heap l ≠ e_cmp s.stack) :
    step [Prog| v ≔ cas(e_loc, e_cmp, e_val)] inner s
    = inner [Prog| ↓] (substituteStack s v 0) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_cas_of_neq_of_deterministic s inner h_l h_alloc h_ne
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_cas_of_neq_of_deterministic s inner h_l h_alloc h_ne]

theorem tsum_cas_of_deterministic_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↯] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_cas_error_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↯], s⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics compareAndSetSmallStepSemantics iteOneZero ite_unit
    simp only [not_exists, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_or, not_and,
      not_forall, Decidable.not_not, and_imp, forall_exists_index]
    intro h' l h_l
    exfalso
    exact h' l h_l (h l h_l)

theorem step_cas_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    step [Prog| v ≔ cas(e_loc, e_cmp, e_val)] inner s = inner [Prog| ↯] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_cas_of_deterministic_of_error s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_cas_of_deterministic_of_error s inner h]

theorem tsum_alloc_of_allocation (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} {n : ℕ} ( h_n : e s.stack = ↑n) (h_allocable : isNotAlloc s.heap l n) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack (allocateHeap s l n) v l) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_alloc_support_superset s h_n
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack (allocateHeap s l n) v l)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics allocateSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and,
      not_or]
    intro h
    exfalso
    exact h l rfl n h_n.symm h_allocable rfl

theorem step_alloc (s : State Var) (inner : Program Var → StateRV Var)
    {n : ℕ} ( h_n : e s.stack = ↑n)  :
    step [Prog| v ≔ alloc(e)] inner s
    = sInf { x | ∃ l, isNotAlloc s.heap l n
      ∧ x = inner [Prog| ↓] (substituteStack (allocateHeap s l n) v l)} := by
  unfold step
  apply le_antisymm
  · apply sInf_le_sInf
    rintro _ ⟨l, h_notAlloc, rfl⟩
    use (allocation l)
    apply And.intro
    · rw [enabledAction, if_pos]
      · use l, rfl, n, h_n.symm
      · use n, h_n.symm
    · exact tsum_alloc_of_allocation s inner h_n h_notAlloc
  · apply sInf_le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    rw [enabledAction, if_pos] at h_a
    · obtain ⟨l, h_l, n', h_n', h_notAlloc'⟩ := h_a
      rw [h_n,Nat.cast_inj] at h_n'
      rw [h_n'] at h_notAlloc'
      rw [h_l]
      use l, h_notAlloc', tsum_alloc_of_allocation s inner h_n h_notAlloc'
    · use n, h_n.symm

theorem tsum_alloc_of_deterministic_of_error (s : State Var) (inner : Program Var → StateRV Var)
    ( h_n : ∀ n : ℕ, e s.stack ≠ ↑n) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ alloc(e)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↯] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_alloc_error_support_superset s
  · rw [tsum_singleton (⟨[Prog| ↯], s⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ alloc(e)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics allocateSmallStepSemantics iteOneZero ite_unit
    simp only [not_exists, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_forall,
      Decidable.not_not, forall_exists_index]
    intro n' h_n'
    exfalso
    exact h_n n' h_n'.symm

theorem step_alloc_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ n : ℕ, e s.stack ≠ ↑n) :
    step [Prog| v ≔ alloc(e)] inner s = inner [Prog| ↯] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction]
    apply And.intro
    · rw [if_neg]
      · rfl
      · simp only [not_exists]; intro n h_n; exact h n h_n.symm
    · exact tsum_alloc_of_deterministic_of_error s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction] at h_a
    rw [if_neg] at h_a
    · rw [h_a, tsum_alloc_of_deterministic_of_error s inner h]
    · simp only [not_exists]; intro n h_n; exact h n h_n.symm

theorem tsum_free_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ}
    ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s.heap l n) :
    (∑' cs : progState,
    (semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (freeHeap s l n) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_free_support_superset s h_l h_n h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (freeHeap s l n)⟩ : progState)
      (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics freeSmallStepSemantics iteOneZero ite_unit
    simp only [true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l n h_n h_alloc rfl

theorem step_free (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ}
    ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s.heap l n) :
    step [Prog| free(e_loc, e_val)] inner s
    = inner [Prog| ↓] (freeHeap s l n) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_free_of_deterministic s inner h_l h_n h_alloc
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_free_of_deterministic s inner h_l h_n h_alloc]

theorem tsum_free_of_deterministic_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ (x : ℕ+), ↑↑x = e_loc s.stack → ∀ (x_1 : ℕ), ↑x_1 = e_val s.stack → ¬isAlloc s.heap x x_1) :
    (∑' cs : progState,
    (semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↯] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_free_error_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↯], s⟩ : progState)
      (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics freeSmallStepSemantics iteOneZero ite_unit
    simp only [not_exists, exists_and_right, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff,
      not_or, not_and, not_not, not_forall, Decidable.not_not, forall_exists_index, and_imp]
    intro h' h'' l h_l
    obtain ⟨n, h_n⟩ := h'' l h_l
    exfalso
    exact h l h_l.symm n h_n <| h' l h_l n h_n

theorem step_free_of_error (s : State Var) (inner : Program Var → StateRV Var)
    (h : ∀ (x : ℕ+), ↑↑x = e_loc s.stack → ∀ (x_1 : ℕ), ↑x_1 = e_val s.stack → ¬isAlloc s.heap x x_1) :
    step [Prog| free(e_loc, e_val)] inner s = inner [Prog| ↯] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_free_of_deterministic_of_error s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_free_of_deterministic_of_error s inner h]

theorem tsum_probChoice_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = (e s.stack) * inner c₁ s + σ (e s.stack) * inner c₂ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_probChoice_support_superset s
  · cases eq_or_ne c₂ c₁ with
    | inl h_eq =>
      rw [h_eq, Set.pair_eq_singleton]
      rw [tsum_singleton (⟨c₁, s⟩ : progState)
        (fun cs : progState => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
      unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics
      simp only [and_self, ↓reduceIte, one_mul, truncatedAdd_symm_eq]
    | inr h_ne =>
      have : (⟨c₁, s⟩ : progState) ≠ ⟨c₂, s⟩ := by simp [Prod.mk.inj_iff, Ne.symm h_ne]
      rw [tsum_pair (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) this]
      unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics
      simp only [and_self, ↓reduceIte, true_and, ite_mul, one_mul, and_true]
      rw [if_neg (by simp only [h_ne, and_false, not_false_eq_true])]
      rw [if_neg (by simp only [Ne.symm h_ne, and_true, not_false_eq_true])]
      rw [if_neg (Ne.symm h_ne)]

theorem step_probChoice (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| pif e then [[c₁]] else [[c₂]] fi] inner s
    = (e s.stack) * inner c₁ s + σ (e s.stack) * inner c₂ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_probChoice_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_probChoice_of_deterministic s inner]

theorem tsum_condChoice_left_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true) :
    (∑' cs : progState,
    (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c₁ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_left_support_superset s h
  · rw [tsum_singleton (⟨c₁, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics
    simp only [h, and_self, not_true_eq_false, false_and, or_false, iteOneZero_true, one_mul]

theorem step_condChoice_left (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = inner c₁ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_condChoice_left_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_condChoice_left_of_deterministic s inner h]

theorem tsum_condChoice_right_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false) :
    (∑' cs : progState,
    (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c₂ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_right_support_superset s h
  · rw [tsum_singleton (⟨c₂, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics
    simp only [h, Bool.false_eq_true, false_and, not_false_eq_true, and_self, or_true,
      iteOneZero_true, one_mul]

theorem step_condChoice_right (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = inner c₂ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_condChoice_right_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_condChoice_right_of_deterministic s inner h]

theorem tsum_loop_cont_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true) :
    (∑' cs : progState,
    (semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| [[c]] ; while e begin [[c]] fi] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_cont_support_superset s h
  · rw [tsum_singleton (⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics loopSmallStepSemantics
    simp only [h, and_self, iteOneZero_true, one_mul]

theorem step_loop_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true):
    step [Prog| while e begin [[c]] fi] inner s
    = inner [Prog| [[c]] ; while e begin [[c]] fi] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_loop_cont_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_loop_cont_of_deterministic s inner h]

theorem tsum_loop_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false) :
    (∑' cs : progState,
    (semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_term_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↓], s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics loopSmallStepSemantics
    simp only [h, Bool.false_eq_true, not_false_eq_true, and_self, iteOneZero_true, one_mul]

theorem step_loop_term (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false):
    step [Prog| while e begin [[c]] fi] inner s
    = inner [Prog| ↓] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_loop_term_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_loop_term_of_deterministic s inner h]

theorem tsum_sequential_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| ↓ ; [[c]]] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_sequential_term_support_superset s
  · rw [tsum_singleton (⟨c, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics
    simp only [↓reduceIte, and_self, iteOneZero_true, one_mul]

theorem step_sequential_term (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↓ ; [[c]]] inner s
    = inner c s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, ↓reduceIte, Set.mem_singleton_iff, true_and]
    exact tsum_sequential_term_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_sequential_term_of_deterministic s inner]

theorem step_qslSepMul_eq_qslSepMul_step (h : (writtenVarProgram c) ∩ (varStateRV P) = ∅)
    (h_abort : inner [Prog| ↯] = `[qsl| qFalse]):
    `[qsl| [[step c inner]] ⋆ [[P]]] ⊢ step c (fun c' => `[qsl| [[inner c']] ⋆ [[P]]]) := by
  rw [entailment_iff_le]
  intro s
  rw [qslSepMul]
  apply sSup_le
  rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
  induction c generalizing inner with
  | terminated => rw [step_terminated, step_terminated]; exact le_one'
  | error => rw [step_error, step_error]; exact le_one'
  | skip' =>
    rw [step_skip, step_skip]
    apply le_sSup
    use heap₁, heap₂
  | assign v e =>
    rw [step_assign, step_assign]
    apply le_sSup_of_le
    use heap₁, heap₂, h_disjoint, h_union
    rw [Subtype.mk_le_mk]
    simp only [substituteStack, Set.Icc.coe_mul]
    cases eq_or_ne (inner [Prog| ↓] ⟨substituteVar s.stack v (e s.stack), heap₁⟩) 0 with
    | inl h_eq => rw [h_eq]; simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_ne =>
      rw [mul_le_mul_left]
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        rw [substituteVar_eq_of_not_varStateRV h (e s.stack)]
      · rw [ne_eq, Subtype.mk_eq_mk] at h_ne
        exact lt_of_le_of_ne nonneg' (Ne.symm h_ne)
  | manipulate e_loc e_val =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      rw [step_manipulate ⟨s.stack, heap₁⟩ _ h_l h_alloc]
      have h_heap : s.heap l ≠ undef := by
        rw [← h_union]; exact ne_undef_of_union_of_ne_undef h_alloc
      rw [step_manipulate s _ h_l h_heap]
      simp only [substituteHeap, ge_iff_le]
      apply le_sSup_of_le
      · use (substituteLoc heap₁ l (e_val s.stack)), heap₂
        rw [substituteLoc_disjoint h_alloc]
        use h_disjoint
        rw [← h_union]
        use substituteLoc_union
      · exact le_rfl
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_manipulate_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | lookup v e_loc =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      rw [undef_iff_exists_val] at h_alloc
      obtain ⟨q, h_alloc⟩ := h_alloc
      rw [step_lookup ⟨s.stack, heap₁⟩ _ h_l h_alloc]
      have h_heap : s.heap l = q := by
        rw [← h_union]; exact union_val_of_val h_alloc
      rw [step_lookup s _ h_l h_heap]
      apply le_sSup_of_le
      · use heap₁, heap₂, h_disjoint, h_union
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        simp only [substituteStack]
        rw [substituteVar_eq_of_not_varStateRV h q]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_lookup_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | compareAndSet v e_loc e_cmp e_val =>
    by_cases h_alloc : ∃ l : ℕ+, e_loc s.stack = ↑ l ∧ heap₁ l ≠ undef
    case pos =>
      obtain ⟨l, h_l, h_alloc⟩ := h_alloc
      have h_value := undef_iff_exists_val.mp h_alloc
      obtain ⟨q, h_value⟩ := h_value
      by_cases h_q : q = (e_cmp s.stack)
      case pos =>
        rw [h_q] at h_value
        rw [step_cas_of_eq ⟨s.stack, heap₁⟩ _ h_l h_value]
        have h_heap : s.heap l = (e_cmp s.stack) := by
          rw [← h_union]; exact union_val_of_val h_value
        rw [step_cas_of_eq s _ h_l h_heap]
        simp only [substituteStack, substituteHeap, ge_iff_le]
        apply le_sSup_of_le
        · use (substituteLoc heap₁ l (e_val s.stack)), heap₂
          rw [substituteLoc_disjoint h_alloc]
          use h_disjoint
          rw [← h_union]
          use substituteLoc_union
        · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
          simp only [substituteStack]
          rw [substituteVar_eq_of_not_varStateRV h 1]
      case neg =>
        have h_ne_val : heap₁ l ≠ e_cmp s.stack := by
          intro h; simp only [h, val.injEq] at h_value; exact h_q h_value.symm
        rw [step_cas_of_neq ⟨s.stack, heap₁⟩ _ h_l h_alloc h_ne_val]
        have h_alloc' : s.heap l ≠ undef := by
          rw [← h_union]; exact ne_undef_of_union_of_ne_undef h_alloc
        have h_ne_val' : s.heap l ≠ e_cmp s.stack := by
          intro h; rw [← h_union, union_val_iff_of_val h_alloc] at h; exact h_ne_val h
        rw [step_cas_of_neq s _ h_l h_alloc' h_ne_val']
        simp only [substituteStack, ge_iff_le]
        apply le_sSup_of_le
        · use heap₁, heap₂, h_disjoint, h_union
        · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
          simp only [substituteStack]
          rw [substituteVar_eq_of_not_varStateRV h 0]
    case neg =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_alloc
      rw [step_cas_of_error _ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | allocate v e_n =>
    by_cases h_m : ∃ m : ℕ, e_n s.stack = ↑m
    case pos =>
      obtain ⟨m, h_m⟩ := h_m
      rw [step_alloc ⟨s.stack, heap₁⟩ _ h_m]
      rw [step_alloc s _ h_m]
      apply le_sInf
      rintro _ ⟨l,h_ne_alloc, rfl⟩
      rw [← h_union, isNotAlloc_union] at h_ne_alloc
      apply le_sSup_of_le
      · use (allocateLoc heap₁ l m), heap₂
        use (disjoint_allocateLoc h_disjoint h_ne_alloc.right)
        simp only [substituteStack, allocateHeap, ← h_union]
        use allocateLoc_union
      · simp only [writtenVarProgram, Set.singleton_inter_eq_empty] at h
        simp only [substituteStack]
        rw [substituteVar_eq_of_not_varStateRV h l]
        refine unit_mul_le_mul ?_ le_rfl
        apply sInf_le
        use l, h_ne_alloc.left
        simp only [allocateHeap]
    case neg =>
      simp only [not_exists] at h_m
      rw [step_alloc_of_error ⟨s.stack, heap₁⟩ _ h_m, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | free' e_loc e_n =>
    by_cases h_alloc : ∃ l : ℕ+, l = (e_loc s.stack) ∧ ∃ n : ℕ, n = (e_n s.stack) ∧ isAlloc heap₁ l n
    case pos =>
      obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h_alloc
      rw [step_free ⟨s.stack, heap₁⟩ _ h_l h_n h_alloc]
      have : isAlloc s.heap l n := by rw [← h_union]; exact isAlloc_union h_alloc
      rw [step_free _ _ h_l h_n this]
      simp only [freeHeap, ge_iff_le]
      apply le_sSup
      use (freeLoc heap₁ l n), heap₂, (disjoint_freeLoc h_disjoint)
      simp only [← h_union]
      use union_freeLoc h_alloc h_disjoint
    case neg =>
      simp only [not_exists, not_and] at h_alloc
      rw [step_free_of_error ⟨s.stack, heap₁⟩ _ h_alloc, h_abort]
      simp only [qslFalse, zero_mul, zero_le]
  | probabilisticChoice e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    rw [step_probChoice, step_probChoice]
    rw [right_distrib_of_unit]
    pick_goal 2
    · simp only [Set.Icc.coe_mul, coe_symm_eq]
      exact (add_symm_mem_unitInterval _ _ _).right
    · apply add_le_add
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂
      · rw [mul_assoc]
        refine mul_le_mul le_rfl ?_ nonneg' nonneg'
        apply le_sSup
        use heap₁, heap₂
  | conditionalChoice e c₁ c₂ ih₁ ih₂ =>
    clear ih₁ ih₂
    cases Bool.eq_false_or_eq_true (e s.stack) with
    | inl h_true =>
      rw [step_condChoice_left _ _ h_true]
      rw [step_condChoice_left ⟨s.stack, heap₁⟩ _ h_true]
      apply le_sSup
      use heap₁, heap₂
    | inr h_false =>
      rw [step_condChoice_right _ _ h_false]
      rw [step_condChoice_right ⟨s.stack, heap₁⟩ _ h_false]
      apply le_sSup
      use heap₁, heap₂
  | loop e c ih =>
    clear ih
    cases Bool.eq_false_or_eq_true (e s.stack) with
    | inl h_true =>
      rw [step_loop_cont _ _ h_true]
      rw [step_loop_cont ⟨s.stack, heap₁⟩ _ h_true]
      apply le_sSup
      use heap₁, heap₂
    | inr h_false =>
      rw [step_loop_term _ _ h_false]
      rw [step_loop_term ⟨s.stack, heap₁⟩ _ h_false]
      apply le_sSup
      use heap₁, heap₂
  | sequential c₁ c₂ ih₁ ih₂ =>
    clear ih₂
    cases eq_or_ne c₁ [Prog| ↓] with
    | inl h_term =>
      rw [h_term, step_sequential_term, step_sequential_term]
      apply le_sSup
      use heap₁, heap₂
    | inr h_ne_term =>
      rw [step_sequential_cont _ _ h_ne_term h_abort]
      have : `[qsl| [[inner [Prog| ↯] ]] ⋆ [[P]]] = `[qsl| qFalse] := by {
        apply funext
        intro s'
        apply le_antisymm
        · apply sSup_le
          rintro _ ⟨_, _, _, _, rfl⟩
          rw [h_abort]
          simp only [qslFalse, zero_mul, le_refl]
        · simp only [qslFalse, zero_le]
      }
      rw [step_sequential_cont _ _ h_ne_term this]
      simp only [writtenVarProgram, Set.union_inter_distrib_right, Set.union_empty_iff] at h
      specialize @ih₁ (fun c' => if c' = [Prog| ↯] then inner [Prog| ↯] else inner [Prog| [[c']] ; [[c₂]]]) h.left
      apply le_trans (ih₁ (by rw [if_pos rfl, h_abort]))
      apply monotone_step
      rw [Pi.le_def]
      intro c
      split
      · exact le_rfl
      · exact le_rfl


  | concurrent c₁ c₂ ih₁ ih₂ => sorry




end CQSL
