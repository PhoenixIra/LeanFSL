import InvLimDiss.Program.Semantics
import Mathlib.Algebra.Group.Support

/-!
  This file features lemmas about the support of the probability transition function.
-/

namespace Semantics

open Action Syntax unitInterval State HeapValue

variable {Var : Type}

/-- A program state is a program with a state-/
abbrev progState := (Program Var) × (State Var)

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
    (fun cs : progState => semantics [Prog| skip] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], s⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics skipSmallStepSemantics at h
  rw [iteOneZero_eq_zero_def] at h
  simp only [true_and, not_and, Classical.not_imp, not_not] at h
  rw [Set.mem_singleton_iff, Prod.mk.inj_iff]
  exact ⟨h.left, h.right.symm⟩

theorem tsum_assign_support_superset (s : State Var) :
    (fun cs : progState => semantics [Prog| v ≔ e] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack s v (e s.stack))⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics assignSmallStepSemantics at h
  split at h
  case h_1 h_c =>
    simp only [true_and, iteOneZero_eq_zero_def, not_not] at h
    rw [Set.mem_singleton_iff, Prod.mk.inj_iff]
    exact ⟨h_c, h.symm⟩
  case h_2 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_manipulate_support_superset (s : State Var)
    {l : PNat} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l ≠ undef) :
    (fun cs : progState => semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteHeap s l (e_val s.stack))⟩} := by
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
    rw [Set.mem_singleton_iff, Prod.mk.inj_iff, h_l']
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
    (fun cs : progState => semantics [Prog| e_loc *≔ e_val] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↯], s⟩} := by
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
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h'
    obtain ⟨h_s, _⟩ := h'
    simp only [Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
    use h_c, h_s.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_lookup_support_superset (s : State Var)
    {l : PNat} {value : ℚ} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = value) :
    (fun cs : progState => semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack s v value)⟩} := by
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
    rw [Set.mem_singleton_iff, Prod.mk.inj_iff, h_alloc']
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
    (fun cs : progState => semantics [Prog| v ≔* e_loc] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↯], s⟩} := by
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
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h'
    obtain ⟨h_s, _⟩ := h'
    simp only [Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
    use h_c, h_s.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_cas_of_eq_support_superset (s : State Var)
    {l : PNat} (h_l : e_loc s.stack = ↑l) (h_alloc: s.heap l = e_cmp s.stack) :
    (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack (substituteHeap s l (e_val s.stack)) v 1)⟩} := by
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
      rw [Set.mem_singleton_iff, Prod.mk.inj_iff]
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
    (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack s v 0)⟩} := by
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
    · rw [Set.mem_singleton_iff, Prod.mk.inj_iff]
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
    (fun cs : progState => semantics [Prog| v ≔ cas(e_loc, e_cmp, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↯], s⟩} := by
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
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_or, not_forall,
      Decidable.not_not, Classical.not_imp] at h'
    obtain ⟨h_s, _⟩ := h'
    simp only [Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
    use h_c, h_s.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_alloc_support_superset (s : State Var)
    {l : ℕ+} {n : ℕ} ( h_n : e s.stack = ↑n) :
    (fun cs : progState => semantics [Prog| v ≔ alloc(e)] s (allocation l) cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack (allocateHeap s l n) v l)⟩} := by
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
    rw [h_l', h_n.symm, Set.mem_singleton_iff, Prod.mk.inj_iff]
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
    (fun cs : progState => semantics [Prog| v ≔ alloc(e)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↯], s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics allocateSmallStepSemantics at h'
  split at h'
  case h_1 _ =>
    simp only [substituteStack, allocateHeap, false_and, exists_const, iteOneZero_false,
      not_true_eq_false] at h'
  case h_2 h_c =>
    simp only [not_exists, true_and, iteOneZero_eq_zero_def, not_and, not_forall, Decidable.not_not,
      Classical.not_imp] at h'
    obtain ⟨h_s, _⟩ := h'
    simp only [Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
    use h_c, h_s.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_free_support_superset (s : State Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ}
    ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s.heap l n) :
    (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (freeHeap s l n)⟩} := by
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
    rw [← h_l', ← h_n', Set.mem_singleton_iff, Prod.mk.inj_iff]
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
      rw [← h_l', h_n', not_not]
      exact h_alloc
    · intro _ _
      use n
    · exact h_l.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_free_error_support_superset (s : State Var)
    (h : ∀ (x : ℕ+), ↑↑x = e_loc s.stack → ∀ (x_1 : ℕ), ↑x_1 = e_val s.stack → ¬isAlloc s.heap x x_1) :
    (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↯], s⟩} := by
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
    simp only [not_exists, exists_and_right, true_and, iteOneZero_eq_zero_def, not_and, not_or,
      not_not, not_forall, Decidable.not_not, forall_exists_index, Classical.not_imp] at h'
    obtain ⟨h_s, _⟩ := h'
    simp only [Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
    use h_c, h_s.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h'

theorem tsum_probChoice_support_superset (s : State Var) :
    (fun cs : progState => semantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2).support
    ⊆ {⟨c₁, s⟩, ⟨c₂, s⟩} := by
  intro cs h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics at h
  simp only [true_and, ite_eq_right_iff, Classical.not_imp] at h
  obtain ⟨h_s, h⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff, Prod.mk.inj_iff]
  split at h
  case isTrue h_c =>
    exact Or.inl ⟨h_c.left.symm, h_s.symm⟩
  case isFalse h_ne_c =>
    split at h
    case isTrue h_c₁ =>
      exact Or.inl ⟨h_c₁.symm, h_s.symm⟩
    case isFalse h_ne_c₁ =>
      split at h
      case isTrue h_c₂ =>
        exact Or.inr ⟨h_c₂.symm, h_s.symm⟩
      case isFalse h_ne_c₂ => simp only [not_true_eq_false] at h

theorem tsum_condChoice_left_support_superset (s : State Var) (h : (e s.stack) = true):
    (fun cs : progState => semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2).support
    ⊆ {⟨c₁, s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics at h'
  simp only [Bool.not_eq_true, true_and, iteOneZero_eq_zero_def, not_not] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff]
  obtain ⟨h_s, ⟨_, h'⟩ | ⟨h', _⟩⟩ := h'
  · exact ⟨h'.symm, h_s.symm⟩
  · simp only [h, Bool.true_eq_false] at h'

theorem tsum_condChoice_right_support_superset (s : State Var) (h : (e s.stack) = false):
    (fun cs : progState => semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2).support
    ⊆ {⟨c₂, s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics at h'
  simp only [Bool.not_eq_true, true_and, iteOneZero_eq_zero_def, not_not] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff]
  obtain ⟨h_s, ⟨h', _⟩ | ⟨_, h'⟩⟩ := h'
  · simp only [h, Bool.true_eq_false] at h'
  · exact ⟨h'.symm, h_s.symm⟩

theorem tsum_loop_cont_support_superset (s : State Var) (h : (e s.stack) = true):
    (fun cs : progState => semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics loopSmallStepSemantics at h'
  simp only [h, not_true_eq_false, and_false, iteOneZero_false, and_true, true_and] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff]
  split at h'
  case h_1 _ => simp only [not_true_eq_false] at h'
  case h_2 =>
    simp only [iteOneZero_eq_zero_def, not_and, Classical.not_imp, not_not] at h'
    exact ⟨h'.left, h'.right.symm⟩

theorem tsum_loop_term_support_superset (s : State Var) (h : (e s.stack) = false) :
    (fun cs : progState => semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics loopSmallStepSemantics at h'
  simp only [h, Bool.false_eq_true, not_false_eq_true, and_true, true_and, and_false,
    iteOneZero_false] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff]
  split at h'
  case h_1 h_c =>
    simp only [iteOneZero_eq_zero_def, not_not] at h'
    exact ⟨h_c, h'.symm⟩
  case h_2 =>
    simp only [not_true_eq_false] at h'

theorem tsum_sequential_term_support_superset (s : State Var) :
    (fun cs : progState => semantics [Prog| ↓ ; [[c]]] s deterministic cs.1 cs.2).support
    ⊆ {⟨c, s⟩} := by
  intro cs h'
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h'
  unfold programSmallStepSemantics at h'
  simp only [↓reduceIte, true_and, iteOneZero_eq_zero_def, not_and, Classical.not_imp, not_not] at h'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Prod.mk.inj_iff]
  exact ⟨h'.right, h'.left.symm⟩

theorem tsum_sequential_cont_support_superset (s : State Var) (h : c₁ ≠ [Prog| ↓]) :
    (fun cs : progState => semantics [Prog| [[c₁]] ; [[c₂]]] s a cs.1 cs.2).support
    ⊆ {x | ∃ s', x = ⟨[Prog| ↯], s'⟩} ∪ {x | ∃ c₁' s', x = ⟨[Prog| [[c₁']] ; [[c₂]]], s'⟩} := by
  intro cs h'
  simp only [Function.mem_support, ne_eq] at h'
  unfold programSmallStepSemantics at h'
  simp only [if_neg h] at h'
  simp only [Set.mem_union, Set.mem_setOf_eq]
  split at h'
  case isTrue h_abort =>
    apply Or.inl
    use cs.2
    rw [Prod.mk.inj_iff]
    exact ⟨h_abort, rfl⟩
  case isFalse h_ne_abort =>
    split at h'
    case h_1 c₂' c' h_cs =>
      split at h'
      case isTrue h_c₂ =>
        rw [← h_c₂] at h_cs
        apply Or.inr
        use c₂', cs.2
        rw [Prod.mk.inj_iff]
        exact ⟨h_cs, rfl⟩
      case isFalse => simp only [not_true_eq_false] at h'
    case h_2 => simp only [not_true_eq_false] at h'


end Semantics
