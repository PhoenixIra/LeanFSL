import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
This file contains definitions and lemmas about program states, i.e. stack-heap pairs.
We leave variables as a generic type to allow instantiating fancy variables.
It features:
* Lemmas about PNat as heap only have locations on PNat
* A type for HeapValue, which is essentially isomorph to `Option ℚ`
* Definition of `Stack` and `Heap`, which are functions from variables to `ℚ`,
  and their Pair a `State`. `Heap` here is not necessarily finite, only partial.
* Definitions and Lemmas about changing the values of `Stack` and `Heap` on the `State`.
-/

namespace PNat

theorem add_right_nat {n : PNat} {m : Nat} : 0 < n + m := Nat.add_pos_left n.prop m
theorem add_left_nat {n : Nat} {m : PNat} : 0 < n + m := Nat.add_pos_right n m.prop

instance : HAdd PNat Nat PNat where
  hAdd n m := ⟨n + m, PNat.add_right_nat⟩

instance : HAdd Nat PNat PNat where
  hAdd n m := ⟨n + m, PNat.add_left_nat⟩

end PNat



open Rat Classical

/-- Values of a heap, `undef` for partial values. -/
inductive HeapValue
| val : ℚ → HeapValue
| undef : HeapValue

open HeapValue

instance : Coe ℚ HeapValue where
coe := fun q => val q

/-- A Stack is a map from variables to their values -/
def Stack (Variable : Type) : Type := Variable → ℚ

/-- A Heap is a partial map from positive numbers to values-/
def Heap : Type := PNat → HeapValue

/-- Gets the value at a heap location, given that the heap location is not undefined -/
def getVal (heap : Heap) (l : PNat) (h : heap l ≠ undef) : ℚ :=
match h_eq : heap l with
| val q => q
| undef => by exfalso; exact h h_eq

theorem getVal_eq_self {heap heap' : Heap} {l l' : PNat} (h : heap l ≠ undef) (h_eq : heap' l' = heap l) :
  val (getVal heap l h) = heap' l' := by
rw [h_eq]
unfold getVal
split
case h_1 h => exact h.symm
case h_2 h'=> exfalso; exact h h'

/-- The state, a stack heap pair. -/
structure State (Variable : Type) where
stack : Stack Variable
heap : Heap

variable {Var : Type}

namespace State

instance inhabited_stack : Inhabited (Stack Var) := ⟨fun _ => 0⟩

instance inhabited_heap : Inhabited Heap := ⟨fun _ => undef⟩

instance inhabited_state : Inhabited (State Var) := ⟨fun _ => 0, fun _ => undef⟩

/-- Substitute the value of variable in the Stack-/
@[simp]
noncomputable def substituteVar (s : Stack Var) (v : Var) (q : ℚ) : Stack Var :=
  fun v' => if v = v' then q else s v'

/-- Lifting of `substituteVar` on Stacks-/
noncomputable def substituteStack
    (s : State Var) (v : Var) (q : ℚ) : State Var :=
  ⟨substituteVar s.stack v q,s.heap⟩

-- @[simp]
-- theorem substituteStack_heap {s : State Var} {v : Var} {q : ℚ} :
--     (substituteStack s v q).heap = s.heap := by
--   unfold substituteStack
--   simp only

theorem substituteVar_stack {s : Stack Var} {v : Var} {q : ℚ} :
    (∀ v', v ≠ v' → (substituteVar s v q) v' = s v')
    ∧ (∀ v', v = v' → (substituteVar s v q) v' = q) := by
  apply And.intro
  · intro v' h_ne
    exact (if_neg h_ne)
  · intro v' h_eq
    unfold substituteVar
    rw [ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq


-- theorem substituteVar_def {s s' : State Var} {v : Var} {q : ℚ} :
--     substituteStack s v q = s' ↔ s'.heap = s.heap
--       ∧ (∀ v', v ≠ v' → s'.stack v' = s.stack v')
--       ∧ (∀ v', v = v' → s'.stack v' = q) := by
--   apply Iff.intro
--   · intro h_substitute
--     rw [←h_substitute]
--     exact ⟨substituteStack_heap, substituteStack_stack⟩
--   · intro ⟨h_heap, h_remain, h_changed⟩
--     unfold substituteStack substituteVar
--     rw [State.mk.injEq]
--     apply And.intro
--     · funext v'
--       cases eq_or_ne v v' with
--       | inl h_eq => rw [if_pos h_eq]; exact (h_changed v' h_eq).symm
--       | inr h_ne => rw [if_neg h_ne]; exact (h_remain v' h_ne).symm
--     · exact h_heap.symm

/-- Substitute the value of a heap location on the stack -/
noncomputable def substituteLoc
    (heap : Heap) (l : PNat) (q : ℚ) : Heap :=
  fun l' => if l = l' then val q else heap l'

noncomputable def substituteHeap
    (s : State Var) (l : PNat) (q : ℚ) : State Var :=
  ⟨s.stack, substituteLoc s.heap l q⟩

-- theorem substituteHeap_stack {s : State Var} {l : PNat} {q : ℚ} :
--     (substituteHeap s l q).stack = s.stack := by
--   unfold substituteHeap
--   simp only

theorem substituteLoc_heap {heap : Heap} {l : PNat} {q : ℚ} :
    (∀ l', l ≠ l' → (substituteLoc heap l q) l' = heap l')
    ∧ (∀ l', l = l' → (substituteLoc heap l q) l' = val q) := by
  unfold substituteLoc
  apply And.intro
  · intro l' h_ne
    exact (if_neg h_ne)
  · intro l' h_eq
    rw [ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq

-- theorem substituteHeap_def {s s' : State Var} {q : ℚ} :
--     substituteHeap s l q = s' ↔ s'.stack = s.stack
--       ∧ (∀ l', l ≠ l' → s'.heap l' = s.heap l')
--       ∧ (∀ l', l = l' → s'.heap l' = val q) := by
--   apply Iff.intro
--   · intro h_substitute
--     rw [←h_substitute]
--     exact ⟨substituteHeap_stack, substituteHeap_heap⟩
--   · intro ⟨h_stack, h_remain, h_changed⟩
--     unfold substituteHeap substituteLoc
--     rw [State.mk.injEq]
--     apply And.intro
--     · exact h_stack.symm
--     · funext l'
--       cases eq_or_ne l l' with
--       | inl h_eq => rw [if_pos h_eq]; exact (h_changed l' h_eq).symm
--       | inr h_ne => rw [if_neg h_ne]; exact (h_remain l' h_ne).symm

/-- Sets a value location as undefined -/
noncomputable def removeLoc
    (heap : Heap) (l : PNat) : Heap :=
  fun l' => if l = l' then undef else heap l'

noncomputable def removeLocationHeap
    (s : State Var) (l : PNat) : State Var :=
  ⟨s.stack, removeLoc s.heap l⟩

-- theorem removeLocationHeap_stack {s : State Var} {l : PNat} :
--     (removeLocationHeap s l).stack = s.stack := by
--   unfold removeLocationHeap
--   simp only

theorem removeLoc_heap {heap : Heap} {l : PNat} :
    (∀ l', l ≠ l' → (removeLoc heap l) l' = heap l')
    ∧ (∀ l', l = l' → (removeLoc heap l) l' = undef) := by
  unfold removeLoc
  apply And.intro
  · intro l' h_ne
    exact (if_neg h_ne)
  . intro l' h_eq
    rw [ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq

-- lemma removeLocationHeap_def {s s' : State Var} {l : PNat} :
--     removeLocationHeap s l = s' ↔ s'.stack = s.stack
--       ∧ (∀ l', l ≠ l' → s'.heap l' = s.heap l')
--       ∧ (∀ l', l = l' → s'.heap l' = undef) := by
--   apply Iff.intro
--   · intro h_remove
--     rw [←h_remove]
--     exact ⟨removeLocationHeap_stack, removeLocationHeap_heap⟩
--   · intro ⟨h_stack, h_remain, h_changed⟩
--     unfold removeLocationHeap
--     rw [State.mk.injEq]
--     apply And.intro
--     · exact h_stack.symm
--     · funext l'
--       cases eq_or_ne l l' with
--       | inl h_eq =>
--         rw [if_pos h_eq]
--         exact (h_changed l' h_eq).symm
--       | inr h_ne =>
--         rw [if_neg h_ne]
--         exact (h_remain l' h_ne).symm

/-- Checks whether a certain consecutive part of the heap is unallocated. -/
noncomputable def isNotAlloc
    (heap : Heap) (l : PNat) (n : ℕ): Prop :=
  match n with
  | Nat.zero => true
  | Nat.succ n => heap ⟨l+n,PNat.add_right_nat⟩ = undef ∧ isNotAlloc heap l n

theorem isNotAlloc_def (heap : Heap) (l : PNat) (n : ℕ) :
    isNotAlloc heap l n ↔ ∀ l', l ≤ l' → l' < l+n → heap l' = undef := by
  induction n with
  | zero =>
    unfold isNotAlloc; simp only [Nat.zero_eq, add_zero, true_iff]
    intro l' h_le h_lt
    exfalso
    exact not_le_of_lt h_lt h_le
  | succ n ih =>
    unfold isNotAlloc
    apply Iff.intro
    · rintro ⟨h_none, h_alloc⟩ l' h_le h_lt
      rw [Nat.add_succ, Nat.lt_succ] at h_lt
      by_cases h : l' = ⟨l + n, PNat.add_right_nat⟩
      · rw [h]; exact h_none
      · apply ih.mp h_alloc l' h_le
        rw [← PNat.coe_inj, PNat.mk_coe] at h
        exact lt_of_le_of_ne h_lt h
    · intro h
      rw [Nat.add_succ] at h
      apply And.intro
      · apply h ⟨l+n,PNat.add_right_nat⟩
        · rw [← PNat.coe_le_coe, PNat.mk_coe]
          exact le_self_add
        · exact(Nat.lt_succ.mpr le_rfl)
      · have : ∀ l', l ≤ l' → l' < l + n → heap l' = undef := by
          intro l' h_le h_lt
          exact h l' h_le (Nat.lt_succ.mpr <| le_of_lt h_lt)
        exact ih.mpr this

/-- Adds 0 values to a consecutive part of the heap. -/
noncomputable def allocateLoc
    (heap : Heap) (l : PNat) (n : ℕ) : Heap :=
  match n with
  | Nat.zero => heap
  | Nat.succ n => substituteLoc (allocateLoc heap l n) ⟨l+n,PNat.add_right_nat⟩ 0

noncomputable def allocateHeap
    (s : State Var) (l : PNat) (n : ℕ) : State Var :=
  ⟨s.stack, allocateLoc s.heap l n⟩

-- theorem allocateHeap_stack {s : State Var} {l : PNat} {n : ℕ} :
--     (allocateHeap s l n).stack = s.stack := by
--   unfold allocateHeap
--   simp only

theorem allocateLoc_heap {heap : Heap} {l : PNat} {n : ℕ} :
      (∀ l', (l' < l ∨ l+n ≤ l') → (allocateLoc heap l n) l' = heap l')
      ∧ (∀ l', l ≤ l' → l' < l+n → (allocateLoc heap l n) l' = val 0) := by
  apply And.intro
  · induction n with
    | zero => intro l' _; simp only [allocateHeap, allocateLoc]
    | succ n ih =>
      intro l' h_l
      unfold allocateLoc
      cases h_l with
      | inl h_lt =>
        rw [substituteLoc_heap.left l']
        · exact ih l' (Or.inl h_lt)
        · intro h_eq
          rw [← PNat.coe_inj, PNat.mk_coe] at h_eq
          rw [← PNat.coe_lt_coe, ← h_eq, add_lt_iff_neg_left] at h_lt
          exact not_lt_zero' h_lt
      | inr h_le =>
        rw [substituteLoc_heap.left l']
        · rw [Nat.add_succ, Nat.succ_le_iff] at h_le
          apply le_of_lt at h_le
          exact ih l' (Or.inr h_le)
        · intro h_eq
          rw [← PNat.coe_inj, PNat.mk_coe] at h_eq
          rw [← h_eq, add_le_add_iff_left, Nat.succ_le, ← not_le] at h_le
          exact h_le le_rfl
  · intro l' h_l₁ h_l₂
    induction n with
    | zero =>
      rw [add_zero] at h_l₂
      exfalso
      exact not_le_of_lt h_l₂ h_l₁
    | succ n ih =>
      rw [Nat.add_succ] at h_l₂
      cases lt_or_eq_of_le (Nat.le_of_lt_succ h_l₂) with
      | inl h_lt =>
        specialize ih h_lt
        unfold allocateLoc
        rw [substituteLoc_heap.left l']
        · exact ih
        · intro h
          rw [← PNat.coe_inj, PNat.mk_coe] at h
          exact (ne_of_lt h_lt).symm h
      | inr h_eq =>
        unfold allocateLoc
        apply substituteLoc_heap.right l'
        rw [← PNat.coe_inj, PNat.mk_coe]
        exact h_eq.symm

lemma allocateLoc_remain (heap : Heap) (l : PNat) (n : ℕ) :
    ∀ l', (l' < l ∨ l+n ≤ l') → (allocateLoc heap l n) l' = heap l' := by
  induction n with
  | zero => intro l' _; unfold allocateLoc; rfl
  | succ n ih =>
    intro l' h_l'
    unfold allocateLoc
    cases h_l' with
    | inl h =>
      have : ⟨l+n,PNat.add_right_nat⟩ ≠ l' := by {
        intro h_eq
        rw [← PNat.coe_lt_coe, ← h_eq, PNat.mk_coe, add_lt_iff_neg_left] at h
        exact not_lt_zero' h
      }
      rw [substituteLoc_heap.left l' this]
      exact ih l' (Or.inl h)
    | inr h =>
      rw [Nat.add_succ, Nat.succ_le] at h
      cases eq_or_ne ⟨l+n,PNat.add_right_nat⟩ l' with
      | inl h_eq =>
        exfalso
        rw [← PNat.coe_inj, PNat.mk_coe] at h_eq
        exact (ne_of_lt h) h_eq
      | inr h_ne => rw [substituteLoc_heap.left l' h_ne]; exact ih l' (Or.inr <| le_of_lt h)

lemma allocateHeap_change (heap : Heap) (l : PNat) (n : ℕ) :
    ∀ l', l ≤ l' → l' < ⟨l+n,PNat.add_right_nat⟩ → (allocateLoc heap l n) l' = val 0 := by
  induction n with
  | zero =>
    intro l' h_le h_lt
    rw [← PNat.coe_lt_coe, PNat.mk_coe, add_zero] at h_lt
    exfalso
    exact not_le_of_lt h_lt h_le
  | succ n ih =>
    intro l' h_le h_lt
    unfold allocateLoc
    rw [← PNat.coe_lt_coe, PNat.mk_coe, Nat.add_succ, Nat.lt_succ] at h_lt
    by_cases h : l' = ⟨l + n, PNat.add_right_nat⟩
    · exact substituteLoc_heap.right l' h.symm
    · rw [substituteLoc_heap.left l' (Ne.symm h)]
      exact ih l' h_le (lt_of_le_of_ne h_lt h)

-- theorem allocateHeap_def {s s' : State Var} {l : PNat} {n : ℕ} :
--     allocateHeap s l n = s' ↔ s.stack = s'.stack
--       ∧ (∀ l', (l' < l ∨ l+n ≤ l') → s'.heap l' = s.heap l')
--       ∧ (∀ l', l ≤ l' → l' < l+n → s'.heap l' = val 0) := by
--   apply Iff.intro
--   . intro h_alloc; rw [← h_alloc]
--     exact ⟨allocateHeap_stack.symm, allocateHeap_heap⟩
--   · intro ⟨h_stack, h_remain, h_changed⟩
--     rw [State.mk.injEq, ← h_stack]
--     apply And.intro allocateHeap_stack
--     funext l'
--     by_cases h : l' < l ∨ l+n ≤ l'
--     · rw [h_remain l' h]
--       exact allocateHeap_remain s l n l' h
--     · rw [not_or, not_lt, not_le] at h
--       obtain ⟨h_le, h_lt⟩ := h
--       rw [h_changed l' h_le h_lt]
--       exact allocateHeap_change s l n l' h_le h_lt

/-- Checks whether a certain part of the heap is allocated
  (i.e. the reverse but not negation of `isNotAlloc`). -/
noncomputable def isAlloc (heap : Heap) (l : PNat) (n : ℕ) : Prop :=
  match n with
  | 0 => true
  | Nat.succ n => (∃ v, heap ⟨l+n,PNat.add_right_nat⟩ = val v) ∧ isAlloc heap l n

theorem isAlloc_def (heap : Heap) (l : PNat) (n : ℕ) :
    isAlloc heap l n ↔ ∀ l', l ≤ l' → l' < l+n → ∃ x, heap l' = val x := by
  induction n with
  | zero =>
    unfold isAlloc; simp only [Nat.zero_eq, add_zero, true_iff]
    intro l' h_le h_lt
    exfalso
    exact not_le_of_lt h_lt h_le
  | succ n ih =>
    unfold isAlloc
    apply Iff.intro
    · rintro ⟨⟨x, h_some⟩, h_alloc⟩ l' h_le h_lt
      rw [Nat.add_succ, Nat.lt_succ] at h_lt
      by_cases h : l' = ⟨l + n, PNat.add_right_nat⟩
      · use x; rw [h]; exact h_some
      · apply ih.mp h_alloc l' h_le
        rw [← PNat.coe_inj, PNat.mk_coe] at h
        exact lt_of_le_of_ne h_lt h
    · intro h
      rw [Nat.add_succ] at h
      apply And.intro
      · apply h ⟨l+n,PNat.add_right_nat⟩
        · rw [← PNat.coe_le_coe, PNat.mk_coe]; exact le_self_add
        · exact Nat.lt_succ.mpr le_rfl
      · have : ∀ l', l ≤ l' → l' < l + n → ∃ x, heap l' = val x := by
          intro l' h_le h_lt
          exact h l' h_le (Nat.lt_succ.mpr <| le_of_lt h_lt)
        exact ih.mpr this

/-- Removed a consecutive part of the heap. -/
noncomputable def freeLoc
    (heap : Heap) (l : PNat) (n : ℕ) : Heap :=
  match n with
  | 0 => heap
  | Nat.succ n => removeLoc (freeLoc heap l n) ⟨l+n,PNat.add_right_nat⟩

noncomputable def freeHeap
    (s : State Var) (l : PNat) (n : ℕ) : State Var :=
  ⟨s.stack, freeLoc s.heap l n⟩

-- theorem freeHeap_stack {s : State Var} {l : PNat} {n : ℕ} :
--     (freeHeap s l n).stack = s.stack := by
--   unfold freeHeap
--   simp only
--   induction n with
--   | zero => simp only [freeHeap]
--   | succ n ih =>
--     unfold freeHeap freeHeapLoc
--     simp only

theorem freeLoc_heap {heap : Heap} {l : PNat} {n : ℕ} :
      (∀ l', (l' < l ∨ l+n ≤ l') → (freeLoc heap l n) l' = heap l')
      ∧ (∀ l', l ≤ l' → l' < l+n → (freeLoc heap l n) l' = undef) := by
  apply And.intro
  · induction n with
    | zero => intro l' _; simp only [freeLoc]
    | succ n ih =>
      intro l' h_l
      unfold freeLoc
      cases h_l with
      | inl h_lt =>
        rw [removeLoc_heap.left l']
        · exact ih l' (Or.inl h_lt)
        · intro h_eq
          rw [ ← h_eq, ← PNat.coe_lt_coe, PNat.mk_coe, add_lt_iff_neg_left] at h_lt
          exact not_lt_zero' h_lt
      | inr h_le =>
        rw [removeLoc_heap.left l']
        · rw [Nat.add_succ, Nat.succ_le_iff] at h_le
          apply le_of_lt at h_le
          exact ih l' (Or.inr h_le)
        · intro h_eq; rw [← h_eq, PNat.mk_coe, add_le_add_iff_left, Nat.succ_le, ← not_le] at h_le
          exact h_le le_rfl
  · intro l' h_l₁ h_l₂
    induction n with
    | zero =>
      rw [add_zero] at h_l₂
      exfalso
      exact not_le_of_lt h_l₂ h_l₁
    | succ n ih =>
      rw [Nat.add_succ] at h_l₂
      cases lt_or_eq_of_le (Nat.le_of_lt_succ h_l₂) with
      | inl h_lt =>
        specialize ih h_lt
        unfold freeLoc
        rw [removeLoc_heap.left l']
        · exact ih
        · rw [ne_eq, ← PNat.coe_inj, PNat.mk_coe]
          exact (ne_of_lt h_lt).symm
      | inr h_eq =>
        unfold freeLoc
        apply removeLoc_heap.right l'
        rw [← PNat.coe_inj, PNat.mk_coe]
        exact h_eq.symm

lemma freeLoc_remain (heap : Heap) (l : PNat) (n : ℕ) :
    ∀ l', (l' < l ∨ l+n ≤ l') → (freeLoc heap l n) l' = heap l' := by
  induction n with
  | zero => intro l' _; unfold freeLoc; rfl
  | succ n ih =>
    intro l' h_l'
    unfold freeLoc
    cases h_l' with
    | inl h =>
      have : ⟨l+n,PNat.add_right_nat⟩ ≠ l' := by {
        intro h_eq
        rw [← PNat.coe_lt_coe, ← h_eq, PNat.mk_coe, add_lt_iff_neg_left] at h
        exact not_lt_zero' h
      }
      rw [removeLoc_heap.left l' this]
      exact ih l' (Or.inl h)
    | inr h =>
      rw [Nat.add_succ, Nat.succ_le] at h
      cases eq_or_ne ⟨l+n, PNat.add_right_nat⟩ l' with
      | inl h_eq =>
        exfalso
        rw [← PNat.coe_inj, PNat.mk_coe] at h_eq
        exact (ne_of_lt h) h_eq
      | inr h_ne => rw [removeLoc_heap.left l' h_ne]; exact ih l' (Or.inr <| le_of_lt h)

lemma freeHeap_change (heap : Heap) (l : PNat) (n : ℕ) :
    ∀ l', l ≤ l' → l' < l+n → (freeLoc heap l n) l' = undef := by
  induction n with
  | zero => intro l' h_le h_lt; rw [add_zero] at h_lt; exfalso; exact not_le_of_lt h_lt h_le
  | succ n ih =>
    intro l' h_le h_lt
    unfold freeLoc
    rw [Nat.add_succ, Nat.lt_succ] at h_lt
    by_cases h : l' = ⟨l + n, PNat.add_right_nat⟩
    · exact removeLoc_heap.right l' h.symm
    · rw [removeLoc_heap.left l' (Ne.symm h)]
      apply ih l' h_le
      rw [← PNat.coe_inj, PNat.mk_coe] at h
      exact lt_of_le_of_ne h_lt h

-- theorem freeHeap_def {s s' : State Var} {l : PNat} {n : ℕ} :
--     freeHeap s l n = s' ↔ s.stack = s'.stack
--       ∧ (∀ l', (l' < l ∨ l+n ≤ l') → s'.heap l' = s.heap l')
--       ∧ (∀ l', l ≤ l' → l' < l+n → s'.heap l' = undef) := by
--   apply Iff.intro
--   . intro h_alloc; rw [← h_alloc]
--     exact ⟨freeHeap_stack.symm, freeHeap_heap⟩
--   · intro ⟨h_stack, h_remain, h_changed⟩
--     rw [State.mk.injEq, ← h_stack]
--     apply And.intro freeHeap_stack
--     funext l'
--     by_cases h : l' < l ∨ l+n ≤ l'
--     · rw [h_remain l' h]
--       exact freeHeap_remain s l n l' h
--     · rw [not_or, not_lt, not_le] at h
--       obtain ⟨h_le, h_lt⟩ := h
--       rw [h_changed l' h_le h_lt]
--       exact freeHeap_change s l n l' h_le h_lt

/-- States that two heaps are not defined at any same location -/
def disjoint (heap₁ heap₂ : Heap) : Prop := ∀ n, heap₁ n = undef ∨ heap₂ n = undef

theorem disjoint.symm {h₁ h₂ : Heap} (h : disjoint h₁ h₂) : disjoint h₂ h₁ := fun n => Or.symm (h n)

theorem disjoint_comm (h₁ h₂ : Heap) : disjoint h₁ h₂ ↔ disjoint h₂ h₁ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- The left prioritisating union of heaps. -/
instance union : Union Heap
  where union := λ h h' n =>
    match h n with
    | val a => val a
    | undef => h' n

theorem union_comm (heap₁ heap₂ : Heap) (h_disjoint : disjoint heap₁ heap₂) :
    heap₁ ∪ heap₂ = heap₂ ∪ heap₁ := by
  apply funext
  intro n
  simp only [union]
  split
  case h_1 h₁ =>
    split
    case h_1 h₂ =>
      cases h_disjoint n with
      | inl h₁' => rw [h₁'] at h₁; cases h₁
      | inr h₂' => rw [h₂'] at h₂; cases h₂
    case h_2 _ =>
      exact h₁.symm
  case h_2 h =>
    split
    case h_1 h' => exact h'
    case h_2 h' => rw [h, h']

theorem union_assoc (heap₁ heap₂ heap₃ : Heap)  :
    (heap₁ ∪ heap₂) ∪ heap₃ = heap₁ ∪ (heap₂ ∪ heap₃) := by
  apply funext
  intro n
  simp only [union]
  cases heap₁ n
  <;> cases heap₂ n
  <;> cases heap₃ n
  <;> simp

/-- A heap that is everywhere undefined. -/
instance emptyHeap : EmptyCollection Heap := ⟨λ _ => undef⟩

@[simp]
theorem emptyHeap_disjoint (heap : Heap) : disjoint ∅ heap := fun _ => Or.inl rfl

@[simp]
theorem emptyHeap_disjoint' {heap : Heap} : disjoint ∅ heap := emptyHeap_disjoint heap

@[simp]
theorem disjoint_emptyHeap (heap : Heap) : disjoint heap ∅ := by
  rw [disjoint_comm]; exact emptyHeap_disjoint'

@[simp]
theorem disjoint_emptyHeap' {heap : Heap} : disjoint heap ∅ := disjoint_emptyHeap heap


@[simp]
theorem emptyHeap_union (heap : Heap) : ∅ ∪ heap = heap := by
  apply funext; intro n; simp only [union, emptyHeap]

@[simp]
theorem emptyHeap_union' {heap : Heap} : ∅ ∪ heap = heap := emptyHeap_union heap

@[simp]
theorem union_emptyHeap (heap : Heap) : heap ∪ ∅ = heap := by
  rw [union_comm]
  · exact emptyHeap_union'
  · exact disjoint_emptyHeap'

@[simp]
theorem union_emptyHeap' {heap : Heap} : heap ∪ ∅ = heap := union_emptyHeap heap

@[simp]
theorem union_eq_emptyHeap_iff {heap heap' : Heap} :
    heap ∪ heap' = ∅ ↔ heap = ∅ ∧ heap' = ∅ := by
  apply Iff.intro
  · intro h
    obtain h := congrFun h
    simp only [union] at h
    apply And.intro
    · apply funext
      intro n
      specialize h n
      split at h
      case h_1 => cases h
      case h_2 h_undef =>
        rw [h_undef]
        simp only [emptyHeap]
    · apply funext
      intro n
      specialize h n
      split at h
      case h_1 => cases h
      case h_2 => exact h
  · rintro ⟨rfl, rfl⟩
    rw [emptyHeap_union']

theorem ne_undef_of_union_of_ne_undef {heap₁ heap₂ : Heap} {l : PNat}
    (h : heap₁ l ≠ undef) : (heap₁ ∪ heap₂) l ≠ undef := by
  unfold Union.union union
  simp only [ne_eq]
  split
  case h_1 h_val => rw [← h_val]; exact h
  case h_2 h_undef => exfalso; exact h h_undef


/-- Lifting of finite to heap locations. -/
def Heap.Finite (heap : Heap) : Prop := Set.Finite { l | heap l ≠ undef}

namespace Finite

private lemma powerset_finite (heap : Heap) (h_finite : Heap.Finite heap) :
    Set.Finite ({ns : Set PNat | ∀ n ∈ ns, heap n ≠ undef }) := by
  exact Set.Finite.finite_subsets h_finite


open Classical

/-- Helper function for the rest of the proofs -/
private noncomputable def surjectiv_func (heap : Heap) (ns : Set PNat ) : Heap :=
  fun n => if n ∈ ns then heap n else undef

private lemma powerset_surjection (heap : Heap) (h_finite : Heap.Finite heap) :
    Set.Finite (surjectiv_func heap '' { ns : Set PNat | ∀ n ∈ ns, heap n ≠ undef}) := by
  apply Set.Finite.of_surjOn (surjectiv_func heap)
  · intro g h
    exact h
  · exact powerset_finite heap h_finite

/-- Proof that given a finite heap, the set of subheaps is also finite. -/
theorem finite_of_subheaps {heap : Heap} (h_finite : Heap.Finite heap) :
    Set.Finite {heap₁ | ∃ heap₂, heap₁ ∪ heap₂ = heap} := by
  have := powerset_surjection heap h_finite
  simp only [Set.image, ne_eq, Set.mem_setOf_eq] at this
  apply Set.Finite.subset this
  rintro heap₁ ⟨heap₂, h_heap⟩
  use {n | (∃ a, heap₁ n = val a)}
  apply And.intro
  · intro n ⟨_, h_heap₁⟩
    obtain h_heap := congrFun h_heap n
    simp only [Union.union, h_heap₁] at h_heap
    rw [← h_heap]
    simp only [not_false_eq_true]
  · apply funext
    intro n
    obtain h_heap := congrFun h_heap n
    simp only [Union.union] at h_heap
    simp only [surjectiv_func, Set.mem_setOf_eq]
    split
    case isTrue h_heap₁ =>
      obtain ⟨_, h_heap₁⟩ := h_heap₁
      simp only [h_heap₁] at h_heap
      exact Eq.symm <| Eq.trans h_heap₁ h_heap
    case isFalse h_heap₁ =>
      simp only [not_exists] at h_heap₁
      split at h_heap
      case h_1 q h₁ =>
        exfalso
        exact h_heap₁ q h₁
      case h_2 h₁ =>
        exact h₁.symm

end Finite

end State
