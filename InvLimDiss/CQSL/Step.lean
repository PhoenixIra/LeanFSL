import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Quantitative
import InvLimDiss.Program.Support
import InvLimDiss.Program.Enabled
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

open Syntax Semantics QSL unitInterval Action State HeapValue

namespace CQSL

variable {Var : Type}

abbrev progState := (Program Var) × (State Var)
noncomputable abbrev semantics := @programSmallStepSemantics Var

noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : progState, (semantics c s a cs.1 cs.2) * inner cs.1 cs.2 = x}

theorem monotone_step (c : Program Var) : Monotone (step c) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro s
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  apply sInf_le_of_le
  · use a
  · apply tsum_mono
    · exact isSummable _
    · exact isSummable _
    · sorry


theorem tsum_skip_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| skip] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset
    exact tsum_skip_support_superset s
  · rw [tsum_singleton (⟨[Prog| ↓], s⟩ : progState)
      (fun cs : progState => semantics [Prog| skip] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics skipSmallStepSemantics iteOneZero ite_unit
    simp only [and_self, ↓reduceIte, one_mul]

theorem inf_tsum_skip (s : State Var) (inner : Program Var → StateRV Var) :
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
  · apply mul_support_superset
    exact tsum_assign_support_superset s
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack s v (e s.stack))⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ e] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics assignSmallStepSemantics iteOneZero ite_unit
    simp only [and_self, ↓reduceIte, one_mul]

theorem inf_tsum_assign (s : State Var) (inner : Program Var → StateRV Var) :
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
  · apply mul_support_superset
    exact tsum_manipulate_support_superset s h_l h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteHeap s l (e_val s.stack))⟩ : progState)
      (fun cs : progState => semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics manipulateSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l h_alloc rfl

theorem inf_tsum_manipulate (s : State Var) (inner : Program Var → StateRV Var)
    (l : ℕ+) (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) :
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

theorem tsum_lookup_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} {value : ℚ} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = value) :
    (∑' cs : progState,
    (semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack s v value) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset
    exact tsum_lookup_support_superset s h_l h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack s v value)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics lookupSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l.symm value h_alloc rfl

theorem inf_tsum_lookup (s : State Var) (inner : Program Var → StateRV Var)
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

theorem tsum_cas_of_eq_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = e_cmp s.stack) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack (substituteHeap s l (e_val s.stack)) v 1) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset
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

theorem inf_tsum_cas_of_eq (s : State Var) (inner : Program Var → StateRV Var)
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
  · apply mul_support_superset
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

theorem inf_tsum_cas_of_neq (s : State Var) (inner : Program Var → StateRV Var)
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

theorem tsum_alloc_of_allocation (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} {n : ℕ} ( h_n : ↑n = e s.stack) (h_allocable : isNotAlloc s l n) :
    (∑' cs : progState,
    (semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (substituteStack (substituteHeap s l n) v l) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset
    exact tsum_alloc_support_superset s h_n
  · rw [tsum_singleton (⟨[Prog| ↓], (substituteStack (substituteHeap s l n) v l)⟩ : progState)
      (fun cs : progState => semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics allocateSmallStepSemantics iteOneZero ite_unit
    simp only [ne_eq, true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and,
      not_or]
    intro h
    exfalso
    exact h l rfl n h_n h_allocable rfl

theorem inf_tsum_alloc (s : State Var) (inner : Program Var → StateRV Var)
    {n : ℕ} ( h_n : ↑n = e s.stack)  :
    step [Prog| v ≔ alloc(e)] inner s
    = sInf { x | ∃ l, isNotAlloc s l n ∧ x = inner [Prog| ↓] (substituteStack (substituteHeap s l n) v l)} := by
  unfold step
  apply le_antisymm
  · apply sInf_le_sInf
    rintro _ ⟨l, h_notAlloc, rfl⟩
    use (allocation l)
    apply And.intro
    · rw [enabledAction, if_pos]
      · use l, rfl, n
      · use n
    · exact tsum_alloc_of_allocation s inner h_n h_notAlloc
  · apply sInf_le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    rw [enabledAction, if_pos] at h_a
    · obtain ⟨l, h_l, n', h_n', h_notAlloc'⟩ := h_a
      rw [← h_n,Nat.cast_inj] at h_n'
      rw [h_n'] at h_notAlloc'
      rw [h_l]
      use l, h_notAlloc', tsum_alloc_of_allocation s inner h_n h_notAlloc'
    · use n

theorem tsum_free_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ} ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s l n) :
    (∑' cs : progState,
    (semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] (freeHeap s l n) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset
    exact tsum_free_support_superset s h_l h_n h_alloc
  · rw [tsum_singleton (⟨[Prog| ↓], (freeHeap s l n)⟩ : progState)
      (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
    unfold programSmallStepSemantics freeSmallStepSemantics iteOneZero ite_unit
    simp only [true_and, ite_mul, one_mul, zero_mul, ite_eq_left_iff, not_exists, not_and]
    intro h
    exfalso
    exact h l h_l n h_n h_alloc rfl

theorem inf_tsum_free (s : State Var) (inner : Program Var → StateRV Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ} ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s l n) :
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

end CQSL
