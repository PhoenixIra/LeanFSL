import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Defs

/-!
This file contains definitions and lemmas about program states, i.e. stack-heap pairs.
We leave variables as a generic type to allow instantiating fancy variables.
It features:
* Lemmas about PNat as heap only have locations on PNat
* A type for HeapValue, which is essentially isomorph to `Option ℚ`
* Definition of `Stack` and `Heap`, which are functions from variables to `ℚ`,
  and their Pair a `State`. `Heap` here is not necessarily finite, only partial.
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

theorem neq_undef_iff_exists_val {heap : Heap} {l : PNat} :
    heap l ≠ undef ↔ ∃ q, heap l = val q := by
  apply Iff.intro
  · intro h
    cases h_l : (heap l) with
    | val q => use q
    | undef => exfalso; exact h h_l
  · rintro ⟨q, h_l⟩
    rw [h_l]
    simp only [ne_eq, not_false_eq_true]

theorem undef_iff_forall_neq_val {heap : Heap} {l : PNat} :
    heap l = undef ↔ ∀ q, heap l ≠ val q := by
  apply Iff.intro
  · intro h q
    simp only [h, ne_eq, not_false_eq_true]
  · intro h_neq_val
    by_contra h_neq_undef
    rw [← ne_eq, neq_undef_iff_exists_val] at h_neq_undef
    obtain ⟨q, h_q⟩ := h_neq_undef
    apply h_neq_val q
    exact h_q


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
noncomputable def substituteVar (s : Stack Var) (v : Var) (q : ℚ) : Stack Var :=
  fun v' => if v = v' then q else s v'

/-- Lifting of `substituteVar` on Stacks-/
@[simp]
noncomputable def substituteStack
    (s : State Var) (v : Var) (q : ℚ) : State Var :=
  ⟨substituteVar s.stack v q,s.heap⟩

/-- Substitute the value of a heap location on the stack -/
noncomputable def substituteLoc
    (heap : Heap) (l : PNat) (q : ℚ) : Heap :=
  fun l' => if l = l' then val q else heap l'

@[simp]
noncomputable def substituteHeap
    (s : State Var) (l : PNat) (q : ℚ) : State Var :=
  ⟨s.stack, substituteLoc s.heap l q⟩

/-- Sets a value location as undefined -/
noncomputable def removeLoc
    (heap : Heap) (l : PNat) : Heap :=
  fun l' => if l = l' then undef else heap l'

@[simp]
noncomputable def removeLocationHeap
    (s : State Var) (l : PNat) : State Var :=
  ⟨s.stack, removeLoc s.heap l⟩

/-- Checks whether a certain consecutive part of the heap is unallocated. -/
noncomputable def isNotAlloc
    (heap : Heap) (l : PNat) (n : ℕ): Prop :=
  ∀ l', l ≤ l' → l' < l+n → heap l' = undef

/-- Adds 0 values to a consecutive part of the heap. -/
noncomputable def allocateLoc
    (heap : Heap) (l : PNat) (n : ℕ) : Heap :=
  fun l' => if l ≤ l' ∧ l' < l+n then val 0 else heap l'

@[simp]
noncomputable def allocateHeap
    (s : State Var) (l : PNat) (n : ℕ) : State Var :=
  ⟨s.stack, allocateLoc s.heap l n⟩

/-- Checks whether a certain part of the heap is allocated
  (i.e. the reverse but not negation of `isNotAlloc`). -/
noncomputable def isAlloc (heap : Heap) (l : PNat) (n : ℕ) : Prop :=
  ∀ l', l ≤ l' → l' < l+n → heap l' ≠ undef

/-- Removed a consecutive part of the heap. -/
noncomputable def freeLoc
    (heap : Heap) (l : PNat) (n : ℕ) : Heap :=
  fun l' => if l ≤ l' ∧ l' < l+n then undef else heap l'

@[simp]
noncomputable def freeHeap
    (s : State Var) (l : PNat) (n : ℕ) : State Var :=
  ⟨s.stack, freeLoc s.heap l n⟩

def removedHeap
    (heap : Heap) (l : PNat) (n : ℕ) : Heap :=
  fun l' => if l ≤ l' ∧ l' < l+n then heap l' else undef

/-- The disjointness property of heaps -/
def disjoint (heap₁ heap₂ : Heap) : Prop := ∀ n, heap₁ n = undef ∨ heap₂ n = undef

/-- The left prioritisating union of heaps. -/
instance union : Union Heap
  where union := λ h h' n =>
    match h n with
    | val a => val a
    | undef => h' n

/-- A heap that is everywhere undefined. -/
instance emptyHeap : EmptyCollection Heap := ⟨λ _ => undef⟩

def singleton (l : ℕ+) (q : ℚ) : Heap := fun l' => if l = l' then val q else undef

open PNat

def bigSingleton (l : ℕ+) (n : ℕ) (qs : ℕ → ℚ) : Heap :=
  fun l' => if l ≤ l' ∧ l' < l+n then qs (l'-l) else undef

def subset (heap' heap : Heap) : Prop :=
  ∃ heap'', disjoint heap' heap'' ∧ heap = heap' ∪ heap''

noncomputable def heapminus (heap heap' : Heap) : Heap :=
  λ l => if heap' l = undef then heap l else undef

end State
