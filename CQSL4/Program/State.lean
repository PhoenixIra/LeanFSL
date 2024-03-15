import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite

namespace State

open Rat Classical

def Stack (Variable : Type) : Type := Variable → Option ℚ
def Heap : Type := ℕ → Option ℚ

structure State (Variable : Type) where
  stack : Stack Variable
  heap : Heap

variable {Var : Type}


noncomputable def substituteStack
    (s : State Var) (v : Var) (q : ℚ) : State Var :=
  ⟨fun v' => if v = v' then some q else s.stack v',s.heap⟩

theorem substituteStack_heap {s : State Var} {v : Var} {q : ℚ} :
    (substituteStack s v q).heap = s.heap := by
  unfold substituteStack
  simp only

theorem substituteStack_stack {s : State Var} {v : Var} {q : ℚ} :
    (∀ v', v ≠ v' → (substituteStack s v q).stack v' = s.stack v')
    ∧ (∀ v', v = v' → (substituteStack s v q).stack v' = some q) := by
  apply And.intro
  · intro v' h_ne
    exact (if_neg h_ne)
  · intro v' h_eq
    unfold substituteStack
    rw[ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq


theorem substituteStack_def {s s' : State Var} {v : Var} {q : ℚ} :
    substituteStack s v q = s' ↔ s'.heap = s.heap
      ∧ (∀ v', v ≠ v' → s'.stack v' = s.stack v')
      ∧ (∀ v', v = v' → s'.stack v' = q) := by
  apply Iff.intro
  · intro h_substitute
    rw[←h_substitute]
    exact ⟨substituteStack_heap, substituteStack_stack⟩
  · intro h_condition
    unfold substituteStack
    rw[State.mk.injEq]
    apply And.intro
    · funext v'
      cases eq_or_ne v v' with
      | inl h_eq => rw[if_pos h_eq]; exact (h_condition.right.right v' h_eq).symm
      | inr h_ne => rw[if_neg h_ne]; exact (h_condition.right.left v' h_ne).symm
    · exact h_condition.left.symm


noncomputable def substituteHeap
    (s : State Var) (l : ℕ) (q : ℚ) : State Var :=
  ⟨s.stack, fun l' => if l = l' then some q else s.heap l'⟩

theorem substituteHeap_stack {s : State Var} {l : ℕ} {q : ℚ} :
    (substituteHeap s l q).stack = s.stack := by
  unfold substituteHeap
  simp only

theorem substituteHeap_heap {s : State Var} {l : ℕ} {q : ℚ} :
    (∀ l', l ≠ l' → (substituteHeap s l q).heap l' = s.heap l')
    ∧ (∀ l', l = l' → (substituteHeap s l q).heap l' = q) := by
  unfold substituteHeap
  apply And.intro
  · intro l' h_ne
    simp only
    exact (if_neg h_ne)
  · intro l' h_eq
    rw[ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq

theorem substituteHeap_def {s s' : State Var} {v : Var} {q : ℚ} :
    substituteHeap s l q = s' ↔ s'.stack = s.stack
      ∧ (∀ l', l ≠ l' → s'.heap l' = s.heap l')
      ∧ (∀ l', l = l' → s'.heap l' = q) := by
  apply Iff.intro
  · intro h_substitute
    rw[←h_substitute]
    exact ⟨substituteHeap_stack, substituteHeap_heap⟩
  · intro h_condition
    unfold substituteHeap
    rw[State.mk.injEq]
    apply And.intro
    · exact h_condition.left.symm
    · funext l'
      cases eq_or_ne l l' with
      | inl h_eq => rw[if_pos h_eq]; exact (h_condition.right.right l' h_eq).symm
      | inr h_ne => rw[if_neg h_ne]; exact (h_condition.right.left l' h_ne).symm



noncomputable def removeLocationHeap
    (s : State Var) (l : ℕ) : State Var :=
  ⟨s.stack, fun l' => if l = l' then none else s.heap l'⟩

theorem removeLocationHeap_stack {s : State Var} {l : ℕ} :
    (removeLocationHeap s l).stack = s.stack := by
  unfold removeLocationHeap
  simp only

theorem removeLocationHeap_heap {s : State Var} {l : ℕ} :
    (∀ l', l ≠ l' → (removeLocationHeap s l).heap l' = s.heap l')
    ∧ (∀ l', l = l' → (removeLocationHeap s l).heap l' = none) := by
  unfold removeLocationHeap
  apply And.intro
  · intro l' h_ne
    simp only
    exact (if_neg h_ne)
  . intro l' h_eq
    rw[ite_eq_left_iff]
    intro h_ne
    exfalso
    exact h_ne h_eq

lemma removeLocationHeap_def {s s' : State Var} {l : ℕ} :
    removeLocationHeap s l = s' ↔ s'.stack = s.stack
      ∧ (∀ l', l ≠ l' → s'.heap l' = s.heap l')
      ∧ (∀ l', l = l' → s'.heap l' = none) := by
  apply Iff.intro
  · intro h_remove
    rw[←h_remove]
    exact ⟨removeLocationHeap_stack, removeLocationHeap_heap⟩
  · intro h_condition
    unfold removeLocationHeap
    rw[State.mk.injEq]
    apply And.intro
    · exact h_condition.left.symm
    · funext l'
      cases eq_or_ne l l' with
      | inl h_eq =>
        rw[if_pos h_eq]
        exact (h_condition.right.right l' h_eq).symm
      | inr h_ne =>
        rw[if_neg h_ne]
        exact (h_condition.right.left l' h_ne).symm

noncomputable def isNotAlloc
    (s : State Var) (l : ℕ) (n : ℕ): Prop :=
  match n with
  | Nat.zero => true
  | Nat.succ n => s.heap (l+n) = none ∧ isNotAlloc s l n

noncomputable def allocateHeap
    (s : State Var) (l : ℕ) (n : ℕ) : State Var :=
  match n with
  | Nat.zero => s
  | Nat.succ n => substituteHeap (allocateHeap s l n) (l+n) 0

theorem allocateHeap_stack {s : State Var} {l : ℕ} {n : ℕ} :
    (allocateHeap s l n).stack = s.stack := by
  induction n with
  | zero => simp only [allocateHeap]
  | succ n ih =>
    unfold allocateHeap
    rw[substituteHeap_stack]
    exact ih

theorem allocateHeap_heap {s s' : State Var} {l : ℕ} {n : ℕ} :
    (allocateHeap s l n).heap = s'.heap →
      (∀ l', (l' < l ∨ l+n ≤ l') → s'.heap l' = s.heap l')
      ∧ (∀ l', l ≤ l' → l' < l+n → s'.heap l' = some 0) := by
  intro h
  rw[←h]; clear h
  apply And.intro
  · intro l' h_l
    induction n with
    | zero => simp only [allocateHeap]
    | succ n ih =>
      unfold allocateHeap
      cases h_l with
      | inl h_lt =>
        specialize ih (Or.inl h_lt)
        rw[substituteHeap_heap.left l']
        . exact ih
        . apply ne_of_gt
          sorry
      | inr h_le => sorry
  · intro l' h_l₁ h_l₂
    induction n with
    | zero =>
      rw[Nat.zero_eq, add_zero] at h_l₂
      exfalso
      exact not_le_of_lt h_l₂ h_l₁
    | succ n ih =>
      rw[Nat.add_succ] at h_l₂
      cases lt_or_eq_of_le (Nat.le_of_lt_succ h_l₂) with
      | inl h_lt =>
        specialize ih h_lt
        unfold allocateHeap
        rw[substituteHeap_heap.left l' (ne_of_lt h_lt).symm]
        exact ih
      | inr h_eq =>
        unfold allocateHeap
        exact substituteHeap_heap.right l' h_eq.symm


lemma allocateHeap_def {s s' : State Var} {l : ℕ} {n : ℕ} :
    allocateHeap s l n = s' ↔ s.stack = s'.stack
      ∧ ∀ l, ((l' < l ∨ l+n ≤ l') → s.heap l' = s'.heap l')
        ∧ (l ≤ l' → l' < l+n → s'.heap = some 0) := by
  apply Iff.intro
  · intro h_alloc
    unfold allocateHeap at h_alloc
    rw[State.mk.injEq] at h_alloc



noncomputable def isAlloc
    (s : State Var) (l : ℕ) (n : ℕ) : Prop :=
  match n with
  | 0 => true
  | Nat.succ n => ∃ v, s.heap (l+n) = some v ∧ isAlloc s l n

noncomputable def freeHeap
    (s : State Var) (l : ℕ) (n : ℕ) : State Var :=
  match n with
  | 0 => s
  | Nat.succ n => removeLocationHeap (freeHeap s l n) (l+n)

end State
