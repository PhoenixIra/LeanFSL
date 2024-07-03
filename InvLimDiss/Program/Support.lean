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
  intro i h
  simp only [Function.support, ne_eq, Set.mem_setOf_eq] at h
  unfold programSmallStepSemantics skipSmallStepSemantics at h
  rw [iteOneZero_eq_zero_def] at h
  simp only [true_and, not_and, Classical.not_imp, not_not] at h
  rw [Set.mem_singleton_iff, Prod.mk.inj_iff]
  exact ⟨h.left, h.right.symm⟩

theorem tsum_assign_support_superset (s : State Var) :
    (fun cs : progState => semantics [Prog| v ≔ e] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (substituteStack s v (e s.stack))⟩} := by
  intro i h
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
  intro i h
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
  intro i h'
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
  intro i h
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
  intro i h'
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
  intro i h
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
  intro i h
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
  intro i h'
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
  intro i h
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
    obtain ⟨_, h⟩ := h
    exfalso
    exact h n h_n.symm
  case h_3 _ =>
    simp only [not_true_eq_false] at h

theorem tsum_free_support_superset (s : State Var)
    {l : ℕ+} (h_l : ↑l = e_loc s.stack) {n : ℕ}
    ( h_n : ↑n = e_val s.stack) (h_alloc : isAlloc s.heap l n) :
    (fun cs : progState => semantics [Prog| free(e_loc, e_val)] s deterministic cs.1 cs.2).support
    ⊆ {⟨[Prog| ↓], (freeHeap s l n)⟩} := by
  intro i h
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

end Semantics
