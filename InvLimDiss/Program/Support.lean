import InvLimDiss.Program.Semantics
import InvLimDiss.SL.Quantitative
import Mathlib.Algebra.Group.Support
import InvLimDiss.CQSL.Step.ReachState

/-!
  This file features lemmas about the support of the probability transition function.
-/

namespace Semantics

open Action Syntax unitInterval State HeapValue Classical

variable {Var : Type}

/-- For nicer theorems, we abbreviate the probability transition function by semantics -/
noncomputable abbrev semantics := @programSmallStepSemantics Var

theorem mul_support_superset_left {f g : α → I} {s : Set α} (h : f.support ⊆ s) :
    (fun x => f x * g x).support ⊆ s := by
  rintro x h_x
  apply Set.mem_of_subset_of_mem h
  simp only [Function.support, Pi.mul_apply, ne_eq, mul_eq_zero, not_or, Set.mem_setOf_eq] at h_x
  exact h_x.left

theorem mul_support_superset_right {f g : α → I} {s : Set α} (h : g.support ⊆ s) :
    (fun x => f x * g x).support ⊆ s := by
  conv => left; intro a; left; intro a; rw [mul_comm]
  exact mul_support_superset_left h

theorem tsum_skip_support_superset (s : State Var) :
    (fun cs : reachState Var => semantics [Prog| skip] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], s⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics skipSmallStepSemantics at h
  rw [iteOneZero_eq_zero_def] at h
  simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, reachState.state, true_and, not_and,
    Classical.not_imp, not_not] at h
  rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
  exact ⟨h.left, h.right.symm⟩

theorem tsum_assign_support_superset (s : State Var) :
    (fun cs : reachState Var => semantics [Prog| v ≔ e] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteStack s v (e s.stack))⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics assignSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [substituteStack, true_and, iteOneZero_eq_zero_def, not_not] at h
    rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_manipulate_support_superset (s : State Var)
    {l : PNat} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) :
    (fun cs : reachState Var => semantics [Prog| e_loc *≔ e_val] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteHeap s l (e_val s.stack))⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics manipulateSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [ne_eq, true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall,
      Classical.not_imp, not_not] at h
    obtain ⟨l', h_l', h_alloc', h⟩ := h
    rw [h_l] at h_l'
    rw [Nat.cast_inj, PNat.coe_inj] at h_l'
    rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff, h_l']
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h
    obtain ⟨_, h⟩ := h
    exfalso
    apply h
    · intro l' h_l' h_alloc'
      rw [h_l', Nat.cast_inj, PNat.coe_inj] at h_l
      rw [← h_l, h_alloc'] at h_alloc
      simp only [ne_eq, not_true_eq_false] at h_alloc
    · exact h_l
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_manipulate_error_support_superset (s : State Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (fun cs : reachState Var => semantics [Prog| e_loc *≔ e_val] s deterministic cs.prog cs.state).support
    ⊆ ∅ := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics manipulateSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    simp only [ne_eq, true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall,
      Classical.not_imp, not_not] at h'
    obtain ⟨l', h_l', h_alloc', _⟩ := h'
    exfalso
    exact h_alloc' (h l' h_l')
  case h_2 h_c =>
    exfalso
    exact cs.prop h_c
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_lookup_support_superset (s : State Var)
    {l : PNat} {value : ℚ} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = value) :
    (fun cs : reachState Var => semantics [Prog| v ≔* e_loc] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteStack s v value)⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics lookupSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] at h
    obtain ⟨l', h_l', value', h_alloc', h⟩ := h
    rw [h_l] at h_l'
    rw [Nat.cast_inj, PNat.coe_inj] at h_l'
    rw [h_l', h_alloc, val.injEq] at h_alloc'
    rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff, h_alloc']
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [Bool.not_eq_true, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_exists,
      Bool.not_eq_false, not_le, Classical.not_imp, not_lt] at h
    obtain ⟨_, h⟩ := h
    exfalso
    apply h
    · intro l' h_l' h_alloc'
      rw [h_l', Nat.cast_inj, PNat.coe_inj] at h_l
      rw [← h_l, h_alloc'] at h_alloc
      simp only [ne_eq, not_true_eq_false] at h_alloc
    · intro h'
      apply h' l h_l
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_lookup_error_support_superset (s : State Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (fun cs : reachState Var => semantics [Prog| v ≔* e_loc] s deterministic cs.prog cs.state).support
    ⊆ ∅ := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics lookupSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    simp only [ne_eq, true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall,
      Classical.not_imp, not_not] at h'
    obtain ⟨l', h_l', q, h_alloc', _⟩ := h'
    exfalso
    rw [(h l' h_l'.symm)] at h_alloc'
    simp only at h_alloc'
  case h_2 h_c =>
    exfalso
    exact cs.prop h_c
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_cas_of_eq_support_superset (s : State Var)
    {l : PNat} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = e_cmp s.stack) :
    (fun cs : reachState Var =>
      semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteStack (substituteHeap s l (e_val s.stack)) v 1)⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics compareAndSetSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] at h
    obtain ⟨l', h_l', value', h_alloc', h⟩ := h
    rw [h_l] at h_l'
    rw [Nat.cast_inj, PNat.coe_inj] at h_l'
    obtain ⟨_, h⟩ | ⟨h_value', h⟩ := h
    · rw [h_l'] at h
      rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
      exact ⟨h_c, h.symm⟩
    · rw [h_l', h_alloc, val.injEq] at h_alloc'
      exfalso
      exact h_value' h_alloc'.symm
  case h_2 _ =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h
    obtain ⟨_, h⟩ := h
    exfalso
    apply h
    · intro l' h_l' h_alloc'
      rw [h_l', Nat.cast_inj, PNat.coe_inj] at h_l
      rw [← h_l, h_alloc'] at h_alloc
      simp only [ne_eq, not_true_eq_false] at h_alloc
    · exact h_l
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_cas_of_neq_support_superset (s : State Var)
    {l : PNat} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) (h_ne : s.heap l ≠ e_cmp s.stack) :
    (fun cs : reachState Var =>
      semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteStack s v 0)⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics compareAndSetSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] at h
    obtain ⟨l', h_l', value', h_alloc', h⟩ := h
    rw [h_l] at h_l'
    rw [Nat.cast_inj, PNat.coe_inj] at h_l'
    obtain ⟨h_value', h⟩ | ⟨_, h⟩ := h
    · rw [← h_l', h_alloc'] at h_ne
      exfalso
      apply h_ne
      rw [val.injEq]
      exact h_value'
    · rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
      exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h
    obtain ⟨_, h⟩ := h
    exfalso
    apply h
    · intro l' h_l' h_alloc'
      rw [h_l', Nat.cast_inj, PNat.coe_inj] at h_l
      rw [← h_l, h_alloc'] at h_alloc
      simp only [ne_eq, not_true_eq_false] at h_alloc
    · exact h_l
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_cas_error_support_superset (s : State Var)
    (h : ∀ l : ℕ+, e_loc s.stack = ↑l → s.heap l = undef) :
    (fun cs : reachState Var =>
      semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.prog cs.state).support
    ⊆ ∅ := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics compareAndSetSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    simp only [ne_eq, true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, not_not] at h'
    obtain ⟨l', h_l', q, h_alloc', _⟩ := h'
    exfalso
    rw [(h l' h_l'.symm)] at h_alloc'
    simp only at h_alloc'
  case h_2 h_c =>
    exfalso
    exact cs.prop h_c
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_alloc_support_superset (s : State Var)
    {l : ℕ+} {n : ℕ} ( h_n : e s.stack = ↑n) :
    (fun cs : reachState Var => semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (substituteStack (allocateHeap s l n) v l)⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics allocateSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] at h
    obtain ⟨l', h_l', n', h_n', h_notAlloc, h⟩ := h
    rw [allocation.injEq] at h_l'
    rw [← h_n', Nat.cast_inj] at h_n
    rw [h_l', h_n.symm, Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h
    obtain ⟨_, _, h⟩ := h
    exfalso
    exact h n h_n.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h


theorem tsum_alloc_error_support_superset (s : State Var) :
    (fun cs : reachState Var => semantics [Prog| v ≔ alloc(e)] s deterministic cs.prog cs.state).support
    ⊆ ∅ := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics allocateSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    simp only [substituteStack, allocateHeap, false_and, exists_const, iteOneZero_false,
      not_true_eq_false] at h'
  case h_2 h_c =>
    exfalso
    exact cs.prop h_c
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_free_support_superset (s : State Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ}
    ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s.heap l n) :
    (fun cs : reachState Var =>
      semantics [Prog| free(e_loc, e_val)] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], (freeHeap s l n)⟩, by simp⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics freeSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall, Classical.not_imp,
      not_not] at h
    obtain ⟨l', h_l', n', h_n', h_alloc', h⟩ := h
    rw [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
    rw [← h_n, Nat.cast_inj] at h_n'
    rw [← h_l', ← h_n', Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h
    obtain ⟨_, h⟩ := h
    exfalso
    apply h
    · intro l' h_l' n' h_n'
      rw [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
      rw [← h_n, Nat.cast_inj] at h_n'
      rw [← h_l', h_n']
      exact h_alloc
    · intro _ _
      use n
    · exact h_l.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_free_error_support_superset (s : State Var)
    (h : ∀ (x : ℕ+), ↑↑x = e_loc s.stack → ∀ (x_1 : ℕ), ↑x_1 = e_val s.stack → ¬isAlloc s.heap x x_1) :
    (fun cs : reachState Var =>
      semantics [Prog| free(e_loc, e_val)] s deterministic cs.prog cs.state).support
    ⊆ ∅ := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics freeSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    exfalso
    simp only [freeHeap, true_and, iteOneZero_eq_zero_def, not_exists, not_and, not_forall,
      Classical.not_imp, not_not] at h'
    obtain ⟨l, h_l, n, h_n, h_alloc, _⟩ := h'
    exact h l h_l n h_n h_alloc
  case h_2 h_c =>
    exfalso
    exact cs.prop h_c
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_probChoice_support_superset (s : State Var) :
    (fun cs : reachState Var => semantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state).support
    ⊆ (if h : c₁ = [Prog|↯] then ∅ else {⟨⟨c₁, s⟩, by simp [h]⟩})
    ∪ (if h : c₂ = [Prog|↯] then ∅ else {⟨⟨c₂, s⟩, by simp [h]⟩}) := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics at h
  simp only [true_and, ite_eq_right_iff, Classical.not_imp] at h
  obtain ⟨h_s, h⟩ := h
  simp only [reachState.state, ne_eq, Set.mem_setOf_eq] at h_s
  split at h
  case isTrue h_c =>
    apply Set.mem_union_left
    simp only [reachState.prog, ne_eq, Set.mem_setOf_eq] at h_c
    rw [h_c.left, dif_neg cs.prop]
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
    simp only [h_s, and_self]
  case isFalse h_ne_c =>
    simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, not_and] at h_ne_c
    split at h
    case isTrue h_c₁ =>
      apply Set.mem_union_left
      simp only [reachState.prog, ne_eq, Set.mem_setOf_eq] at h_c₁
      rw [h_c₁, dif_neg cs.prop]
      simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
      simp only [h_s, and_self]
    case isFalse h_ne_c₁ =>
      simp only [reachState.prog, ne_eq, Set.mem_setOf_eq] at h_ne_c₁
      split at h
      case isTrue h_c₂ =>
        apply Set.mem_union_right
        simp only [reachState.prog, ne_eq, Set.mem_setOf_eq] at h_c₂
        rw [h_c₂, dif_neg cs.prop]
        simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
        rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
        simp only [h_s, and_self]
      case isFalse h_ne_c₂ => simp only [not_true_eq_false] at h

theorem tsum_condChoice_left_support_superset (s : State Var) (h : (e s.stack) = true):
    (fun cs : reachState Var =>
      semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state).support
    ⊆ if h : c₁ = [Prog| ↯] then ∅ else {⟨⟨c₁, s⟩, by simp [h]⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics at h'
  simp only [reachState.state, ne_eq, Set.mem_setOf_eq, reachState.prog, Bool.not_eq_true, true_and,
    iteOneZero_eq_zero_def, Decidable.not_not] at h'
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq]
  obtain ⟨h_s, ⟨_, h'⟩ | ⟨h', _⟩⟩ := h'
  · rw [h', dif_neg cs.prop]
    rw [Set.mem_singleton_iff, Subtype.mk_eq_mk, Prod.mk.inj_iff]
    simp only [h_s, and_self]
  · simp only [h, Bool.true_eq_false] at h'

theorem tsum_condChoice_right_support_superset (s : State Var) (h : (e s.stack) = false):
    (fun cs : reachState Var =>
      semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state).support
    ⊆ if h : c₂ = [Prog| ↯] then ∅ else {⟨⟨c₂, s⟩, by simp [h]⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics at h'
  simp only [reachState.state, ne_eq, Set.mem_setOf_eq, reachState.prog, Bool.not_eq_true, true_and,
    iteOneZero_eq_zero_def, Decidable.not_not] at h'
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq]
  obtain ⟨h_s, ⟨h', _⟩ | ⟨_, h'⟩⟩ := h'
  · simp only [h, Bool.true_eq_false] at h'
  · rw [h', dif_neg cs.prop]
    simp only [h_s, Prod.mk.eta, Subtype.coe_eta, Set.mem_singleton_iff]

theorem tsum_loop_cont_support_superset (s : State Var) (h : (e s.stack) = true):
    (fun cs : reachState Var =>
      semantics [Prog| while e begin [[c]] fi] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩, by simp⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics loopSmallStepSemantics at h'
  simp only [h, not_true_eq_false, and_false, iteOneZero_false, and_true, true_and] at h'
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
  split at h'
  case h_1 _ => simp only [not_true_eq_false] at h'
  case h_2 =>
    simp only [iteOneZero_eq_zero_def, not_and, Classical.not_imp, not_not] at h'
    exact ⟨h'.left, h'.right.symm⟩

theorem tsum_loop_term_support_superset (s : State Var) (h : (e s.stack) = false) :
    (fun cs : reachState Var =>
      semantics [Prog| while e begin [[c]] fi] s deterministic cs.prog cs.state).support
    ⊆ {⟨⟨[Prog| ↓], s⟩, by simp⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics loopSmallStepSemantics at h'
  simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, reachState.state, h, Bool.false_eq_true,
    not_false_eq_true, and_true, true_and, and_false, iteOneZero_false] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
  split at h'
  case h_1 h_c =>
    simp only [iteOneZero_eq_zero_def, not_not] at h'
    exact ⟨h_c, h'.symm⟩
  case h_2 =>
    simp only [not_true_eq_false] at h'

theorem tsum_sequential_term_support_superset (s : State Var) :
    (fun cs : reachState Var => semantics [Prog| ↓ ; [[c]]] s deterministic cs.prog cs.state).support
    ⊆ if h : c = [Prog|↯] then ∅ else {⟨⟨c, s⟩, by simp [h]⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics at h'
  simp only [↓reduceIte, reachState.state, ne_eq, Set.mem_setOf_eq, reachState.prog, true_and,
    iteOneZero_eq_zero_def, Decidable.not_not] at h'
  rw [← h'.right, dif_neg cs.prop]
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
  exact ⟨rfl, h'.left.symm⟩

-- theorem tsum_sequential_error_support_superset (s : State Var) :
--     (fun cs : reachState Var => semantics [Prog| ↯ ; [[c]]] s deterministic cs.prog cs.state).support
--     ⊆ ∅ := by
--   intro cs h'
--   simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
--   unfold programSmallStepSemantics at h'
--   simp only [↓reduceIte, reachState.state, ne_eq, Set.mem_setOf_eq, reachState.prog, true_and,
--     iteOneZero_eq_zero_def, not_and, Classical.not_imp, Decidable.not_not] at h'
--   exfalso
--   exact cs.prop h'.right

open QSL

theorem tsum_sequential_cont_support_superset (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₁ ≠ [Prog| ↓]) :
    (fun cs : reachState Var =>
      semantics [Prog| [[c₁]] ; [[c₂]]] s a cs.prog cs.state * inner cs.prog cs.state).support
    ⊆ {x | ∃ c₁' s', x = ⟨⟨[Prog| [[c₁']] ; [[c₂]]], s'⟩, by simp⟩
      ∧ semantics [Prog| [[c₁]] ; [[c₂]]] s a [Prog| [[c₁']] ; [[c₂]]] s' ≠ 0
      ∧ inner [Prog| [[c₁']] ; [[c₂]]] s' ≠ 0 } := by
  intro cs h'
  simp only [Function.mem_support, ne_eq] at h'
  unfold programSmallStepSemantics at h'
  simp only [if_neg h_term] at h'
  simp only [Set.mem_union, Set.mem_setOf_eq]
  split at h'
  case isTrue h_abort =>
    exfalso
    exact cs.prop h_abort
  case isFalse =>
    split at h'
    case h_1 c₁' c' h_cs =>
      split at h'
      case isTrue =>
        simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, reachState.state, zero_mul,
          not_true_eq_false] at h'
      case isFalse h_c₁' =>
        split at h'
        case isTrue h_c₂ =>
          rw [← h_c₂] at h_cs
          use c₁', cs.state
          rw [Subtype.mk_eq_mk, Prod.mk.inj_iff]
          use ⟨h_cs, rfl⟩
          simp only [mul_eq_zero, not_or, h_cs] at h'
          apply And.intro
          · unfold programSmallStepSemantics
            rw [if_neg h_term, if_neg (by simp)]
            simp only [↓reduceIte, reachState.state, ne_eq, Set.mem_setOf_eq, ite_eq_left_iff,
              Classical.not_imp]
            use h_c₁'
            exact h'.left
          · exact h'.right
        case isFalse => simp only [zero_mul, not_true_eq_false] at h'
    case h_2 => simp only [zero_mul, not_true_eq_false] at h'


end Semantics
