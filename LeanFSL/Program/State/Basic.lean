import LeanFSL.Program.State.Defs


namespace State

open Rat Classical HeapValue

section substituteVar

theorem substituteVar_substituteVar_of_eq {stack : Stack Var} (h : v = v') :
    substituteVar (substituteVar stack v q) v' q' = substituteVar stack v' q' := by
  apply funext
  intro v''
  simp only [substituteVar]
  split_ifs
  case pos => rfl
  case pos h_neq h_eq =>
    exfalso
    apply h_neq
    rw [← h, h_eq]
  case neg => rfl

theorem substituteVar_substituteVar_of_neq {stack : Stack Var} (h : v ≠ v') :
    substituteVar (substituteVar stack v q) v' q' = substituteVar (substituteVar stack v' q') v q := by
  apply funext
  intro v''
  simp only [substituteVar]
  split_ifs
  case pos h_v' h_v'' =>
    exfalso
    apply h
    rw [h_v', h_v'']
  case neg => rfl
  case pos => rfl
  case neg => rfl

end substituteVar

section disjoint

theorem disjoint.symm {h₁ h₂ : Heap} (h : disjoint h₁ h₂) : disjoint h₂ h₁ := fun n => Or.symm (h n)

theorem disjoint_comm (h₁ h₂ : Heap) : disjoint h₁ h₂ ↔ disjoint h₂ h₁ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

theorem undef_of_disjoint_of_ne_undef {heap₁ heap₂ : Heap} {l : PNat}
    (h : disjoint heap₁ heap₂) (h_undef : heap₁ l ≠ undef) : heap₂ l = undef := by
  specialize h l
  cases h with
  | inl h => exfalso; exact h_undef h
  | inr h => exact h

theorem undef_of_disjoint_of_val {heap₁ heap₂ : Heap} {l : PNat} {q : ℚ}
    (h : disjoint heap₁ heap₂) (h_undef : heap₁ l = q) : heap₂ l = undef := by
  apply undef_of_disjoint_of_ne_undef h
  simp only [h_undef, ne_eq, reduceCtorEq, not_false_eq_true]


theorem substituteLoc_disjoint {heap₁ heap₂ : Heap} {l : PNat} {q : ℚ}
    (h : heap₁ l ≠ undef) : disjoint (substituteLoc heap₁ l q) heap₂ ↔ disjoint heap₁ heap₂ := by
  unfold substituteLoc
  apply Iff.intro
  · intro h_disjoint l'
    cases h_disjoint l' with
    | inl h_disjoint =>
      simp only at h_disjoint
      split at h_disjoint
      case isTrue _ => exfalso; simp only [reduceCtorEq] at h_disjoint
      case isFalse _ => exact Or.inl h_disjoint
    | inr h_disjoint => exact Or.inr h_disjoint
  · intro h_disjoint l'
    simp only
    split
    case isTrue h_l =>
      apply Or.inr
      rw [h_l] at h
      exact undef_of_disjoint_of_ne_undef h_disjoint h
    case isFalse h' => exact h_disjoint l'

theorem disjoint_allocateLoc {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h : disjoint heap₁ heap₂) (h_notAlloc: isNotAlloc heap₂ l m) :
    disjoint (allocateLoc heap₁ l m) heap₂ := by
  intro l'
  by_cases h_l' : l ≤ l' ∧ l' < l + m
  case pos => exact Or.inr <| h_notAlloc l' h_l'.left h_l'.right
  case neg =>
    cases h l' with
    | inr h => exact Or.inr h
    | inl h =>
      apply Or.inl
      simp only [not_and_or, not_le, not_lt] at h_l'
      rw [allocateLoc, if_neg]
      · exact h
      · intro h_l
        cases h_l' with
        | inl h_lt =>
          apply not_le_of_lt h_lt
          exact h_l.left
        | inr h_lt =>
          apply not_le_of_lt h_l.right
          exact h_lt

theorem disjoint_freeLoc {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h : disjoint heap₁ heap₂) : disjoint (freeLoc heap₁ l m) heap₂ := by
  intro l'
  cases h l' with
  | inr h => exact Or.inr h
  | inl h =>
    apply Or.inl
    by_cases h_le : l ≤ l' ∧ l' < l + m
    case pos => simp only [freeLoc, h_le, and_self, ↓reduceIte]
    case neg =>
      simp only [not_and_or, not_le, not_lt] at h_le
      simp only [freeLoc, ite_eq_left_iff, not_and, not_lt]
      intro _
      exact h


end disjoint

section union

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

theorem union_eq_of_left {heap₁ heap₂ : Heap} {l : ℕ+} {q : ℚ} (h : heap₁ l = q) :
    (heap₁ ∪ heap₂) l = q := by
  simp only [Union.union, h]

theorem union_eq_of_left_undef {heap₁ heap₂ : Heap}  (h : heap₁ l = undef) :
    (heap₁ ∪ heap₂) l = heap₂ l := by
  simp only [Union.union, h]

theorem union_eq_of_right_undef {heap₁ heap₂ : Heap}  (h : heap₂ l = undef) :
    (heap₁ ∪ heap₂) l = heap₁ l := by
  simp only [Union.union, h]
  cases (heap₁ l) <;> simp only

theorem substituteLoc_union {heap₁ heap₂ : Heap} {l : PNat} {q : ℚ} :
    (substituteLoc heap₁ l q) ∪ heap₂ = substituteLoc (heap₁ ∪ heap₂) l q := by
  apply funext
  intro l
  simp only [Union.union, union, substituteLoc]
  split
  case h_1 h_eq =>
    rw [← h_eq]
    split
    case isTrue _ => rfl
    case isFalse h_l =>
      rw [if_neg h_l] at h_eq
      rw [h_eq]
  case h_2 h_eq =>
    split at h_eq
    case isTrue _ => exfalso; simp only [reduceCtorEq] at h_eq
    case isFalse h_l =>
      simp only [h_eq, if_neg h_l]

theorem ne_undef_of_union_of_ne_undef {heap₁ heap₂ : Heap} {l : PNat}
    (h : heap₁ l ≠ undef) : (heap₁ ∪ heap₂) l ≠ undef := by
  unfold Union.union union
  simp only [ne_eq]
  split
  case h_1 h_val => rw [← h_val]; exact h
  case h_2 h_undef => exfalso; exact h h_undef

theorem union_val_iff_of_val {heap₁ heap₂ : Heap} {l : PNat}
    (h_alloc : heap₁ l ≠ undef) : (heap₁ ∪ heap₂) l = heap₁ l := by
  unfold Union.union union
  simp only [ne_eq]
  split
  case h_1 h_val => rw [← h_val]
  case h_2 h_undef => exfalso; exact h_alloc h_undef

theorem union_val_of_val {heap₁ heap₂ : Heap} {l : PNat} {q : ℚ}
    (h : heap₁ l = val q) : (heap₁ ∪ heap₂) l = val q := by
  have : heap₁ l ≠ undef := by rw [h]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  rw [union_val_iff_of_val this]
  exact h

theorem union_undef_iff_undef {heap₁ heap₂ : Heap} {l : PNat} :
    (heap₁ ∪ heap₂) l = undef ↔ heap₁ l = undef ∧ heap₂ l = undef := by
  simp only [Union.union]
  apply Iff.intro
  · intro h
    split at h
    case h_1 _ => simp only [reduceCtorEq] at h
    case h_2 h_l => use h_l
  · intro h
    split
    case h_1 h_l => rw [h_l] at h; simp only [reduceCtorEq, false_and] at h
    case h_2 _ => exact h.right

theorem eq_of_union_of_union {heap₁ heap₂ heap₁₂ heap₂₁ : Heap}
    (h₁₂ : heap₁ = heap₂ ∪ heap₁₂) (h₂₁ : heap₂ = heap₁ ∪ heap₂₁) :
    heap₁ = heap₂ := by
  apply funext
  intro l
  have h₁₂_l := congrFun h₁₂ l
  have h₂₁_l := congrFun h₂₁ l
  simp only [union] at h₁₂_l h₂₁_l
  split at h₁₂_l
  case h_1 q h =>
    rw [h₁₂_l, h]
  case h_2 q h =>
    simp only [h₁₂_l] at h₂₁_l ⊢
    split at h₂₁_l
    case h_1 q h' =>
      rw [h', h₂₁_l]
    case h_2 q h' =>
      rw [h', h]

theorem eq_of_union_of_union_left {heap heap₁ heap₂ heap₂' : Heap}
    (h_disjoint : disjoint heap₁ heap₂) (h_union : heap = heap₁ ∪ heap₂)
    (h_disjoint' : disjoint heap₁ heap₂') (h_union' : heap = heap₁ ∪ heap₂') :
    heap₂ = heap₂' := by
  apply funext
  intro l
  cases eq_or_ne (heap₁ l) undef
  case inl h₁_undef =>
    have h_union := congrFun h_union l
    have h_union' := congrFun h_union' l
    rw [union_eq_of_left_undef h₁_undef] at h_union h_union'
    rw [← h_union, ← h_union']
  case inr h₁_def =>
    have h₂_undef := undef_of_disjoint_of_ne_undef h_disjoint h₁_def
    have h₂'_undef := undef_of_disjoint_of_ne_undef h_disjoint' h₁_def
    rw [h₂_undef, h₂'_undef]

theorem disjoint_union_iff (heap₁ heap₂ heap₃ : Heap) :
    disjoint heap₁ (heap₂ ∪ heap₃) ↔ disjoint heap₁ heap₂ ∧ disjoint heap₁ heap₃ := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro l
      cases h l with
      | inl h => exact Or.inl h
      | inr h =>
        rw [union_undef_iff_undef] at h
        exact Or.inr h.left
    · intro l
      cases h l with
      | inl h => exact Or.inl h
      | inr h =>
        rw [union_undef_iff_undef] at h
        exact Or.inr h.right
  · rintro ⟨h₂, h₃⟩
    intro l
    cases h₂ l with
    | inl h₁ => exact Or.inl h₁
    | inr h₂ =>
      cases h₃ l with
      | inl h₁ => exact Or.inl h₁
      | inr h₃ =>
        apply Or.inr
        rw [union_undef_iff_undef]
        exact ⟨h₂, h₃⟩

theorem isNotAlloc_union (heap₁ heap₂ : Heap) (l : ℕ+) (n : ℕ):
    isNotAlloc (heap₁ ∪ heap₂) l n ↔ isNotAlloc heap₁ l n ∧ isNotAlloc heap₂ l n := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro l' h_le h_lt
      specialize h l' h_le h_lt
      rw [union_undef_iff_undef] at h
      exact h.left
    · intro l' h_le h_lt
      specialize h l' h_le h_lt
      rw [union_undef_iff_undef] at h
      exact h.right
  · intro h
    intro l' h_le h_lt
    rw [union_undef_iff_undef]
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨h₁ l' h_le h_lt, h₂ l' h_le h_lt⟩

theorem allocateLoc_union {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ} :
    allocateLoc heap₁ l m ∪ heap₂ = allocateLoc (heap₁ ∪ heap₂) l m := by
  apply funext
  intro l'
  rw [allocateLoc]
  split_ifs
  case pos h =>
    rw [Union.union, union]
    simp only
    split
    case h_1 q h_q =>
      rw [allocateLoc, if_pos h] at h_q
      exact h_q.symm
    case h_2 q h_q =>
      simp only [allocateLoc, if_pos h, reduceCtorEq] at h_q
  case neg h =>
    rw [Union.union, union]
    simp only
    split
    case h_1 q h_q =>
      rw [allocateLoc, if_neg h] at h_q
      simp only [h_q]
    case h_2 q h_q =>
      rw [allocateLoc, if_neg h] at h_q
      simp only [h_q]

theorem isAlloc_of_zero {heap : Heap} : isAlloc heap l 0 := by
  intro l' h_le h_lt
  exfalso
  apply not_le_of_lt h_lt
  simp only [add_zero, PNat.coe_le_coe, h_le]

theorem isAlloc_of_isAlloc_succ {heap : Heap} {l : ℕ+} {m : ℕ} (h : isAlloc heap l (m+1)) :
    isAlloc heap l m := by
  simp only [isAlloc, ne_eq] at h
  simp only [isAlloc, ne_eq]
  intro l' h_le h_lt
  apply h l' h_le
  apply lt_trans h_lt
  simp only [add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one]

theorem isAlloc_union {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h : isAlloc heap₁ l m) : isAlloc (heap₁ ∪ heap₂) l m := by
  intro l' h_le h_lt
  specialize h l' h_le h_lt
  rw [neq_undef_iff_exists_val] at h
  obtain ⟨q, h_q⟩ := h
  simp only [union_eq_of_left h_q, ne_eq, reduceCtorEq, not_false_eq_true]

theorem union_freeLoc {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h_alloc : isAlloc heap₁ l m) (h_disjoint : disjoint heap₁ heap₂) :
    (freeLoc heap₁ l m) ∪ heap₂ = freeLoc (heap₁ ∪ heap₂) l m := by
  apply funext
  intro l'
  by_cases h_l' : l ≤ l' ∧ l' < l + m
  case pos =>
    simp only [Union.union, freeLoc, if_pos h_l']
    specialize h_alloc l' h_l'.left h_l'.right
    cases h_disjoint l' with
    | inl h_undef => exfalso; exact h_alloc h_undef
    | inr h_undef => exact h_undef
  case neg =>
    simp only [freeLoc, if_neg h_l']
    simp only [Union.union]
    simp only [freeLoc, if_neg h_l']

lemma union_freeHeap_removedHeap (heap : Heap) (l : ℕ+) (n : ℕ) :
    heap = freeLoc heap l n ∪ removedHeap heap l n := by
  apply funext
  intro l'
  by_cases l ≤ l' ∧ l' < l+n
  case pos h =>
    rw [union_eq_of_left_undef]
    · simp only [removedHeap]
      rw [if_pos h]
    · simp only [freeLoc, h, and_self, ↓reduceIte]
  case neg h =>
    simp only [Union.union, freeLoc, if_neg h]
    split
    case h_1 h => exact h
    case h_2 h_undef => simp only [h_undef, removedHeap, ite_self]

end union

section free

lemma disjoint_freeLoc_removedHeap {heap : Heap} :
    disjoint (freeLoc heap l n) (removedHeap heap l n) := by
  intro l'
  induction n with
  | zero =>
    apply Or.inr
    simp only [removedHeap, add_zero, PNat.coe_lt_coe, ite_eq_right_iff, and_imp]
    intro h h'
    have := lt_of_le_of_lt h h'
    simp only [lt_self_iff_false] at this
  | succ n ih =>
    cases eq_or_ne l' ⟨l+n,PNat.add_right_nat⟩ with
    | inl h_eq =>
      apply Or.inl
      rw [h_eq]
      simp only [freeLoc, PNat.mk_coe, add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one,
        and_true, ite_eq_left_iff, not_le]
      intro h_lt
      rw [←Subtype.coe_lt_coe, Subtype.coe_mk] at h_lt
      exfalso
      apply not_le_of_lt h_lt
      exact Nat.le_add_right l n
    | inr h_ne =>
      cases ih with
      | inl h_free =>
        apply Or.inl
        simp only [freeLoc, ite_eq_left_iff, not_and, not_lt]
        intro h
        simp only [freeLoc, ite_eq_left_iff, not_and, not_lt] at h_free
        apply h_free
        intro h_lt
        specialize h h_lt
        apply le_trans ?_ h
        simp only [add_le_add_iff_left, le_add_iff_nonneg_right, zero_le]
      | inr h_removed =>
        apply Or.inr
        simp only [removedHeap, ite_eq_right_iff, and_imp] at h_removed
        simp only [removedHeap, ite_eq_right_iff, and_imp]
        intro h_le h_lt
        apply h_removed h_le
        rw [← add_assoc, Nat.lt_succ] at h_lt
        rw [ne_eq, ← Subtype.coe_inj] at h_ne
        exact lt_of_le_of_ne h_lt h_ne

lemma disjoint_singleton_removedHeap {l : ℕ+} {n : ℕ} {heap : Heap} :
    disjoint (singleton ⟨l+n, PNat.add_right_nat⟩ q) (removedHeap heap l n) := by
  intro l'
  by_cases l' = ⟨l+n, PNat.add_right_nat⟩
  case pos h =>
    apply Or.inr
    simp only [removedHeap, ite_eq_right_iff, and_imp]
    intro _ h_lt
    exfalso
    simp only [h, PNat.mk_coe, lt_self_iff_false] at h_lt
  case neg h =>
    apply Or.inl
    simp only [singleton, ite_eq_right_iff, reduceCtorEq, imp_false]
    exact (Ne.symm h)

@[simp]
lemma removedHeap_of_zero {heap : Heap} : removedHeap heap l 0 = ∅ := by
  apply funext
  intro l'
  simp only [removedHeap, add_zero, PNat.coe_lt_coe, emptyHeap, ite_eq_right_iff, and_imp]
  intro h_le h_lt
  have := not_le_of_lt h_lt
  contradiction

lemma removedHeap_of_succ {heap : Heap} :
    removedHeap heap l (n+1)
    = fun l' : ℕ+ => if l' = ⟨l+n, PNat.add_right_nat⟩ then heap l' else removedHeap heap l n l' := by
  apply funext
  intro l'
  split
  case isTrue h =>
    simp only [removedHeap, h, add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one, and_true,
      ite_eq_left_iff, not_le]
    intro h'
    exfalso
    simp only [PNat.mk_coe, add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one, and_true,
      not_le] at h'
    rw [← PNat.coe_lt_coe, PNat.mk_coe] at h'
    simp only [add_lt_iff_neg_left, not_lt_zero'] at h'
  case isFalse h =>
    simp only [removedHeap]
    split
    case isTrue h_l' =>
      rw [if_pos]
      apply And.intro h_l'.left
      apply lt_of_le_of_ne (Nat.le_of_lt_succ h_l'.right)
      rw [← PNat.coe_inj, PNat.mk_coe] at h
      exact h
    case isFalse h_l' =>
      rw [if_neg]
      simp only [not_and, not_lt]
      intro h_le
      simp only [not_and, not_lt] at h_l'
      specialize h_l' h_le
      apply le_trans ?_ h_l'
      simp only [add_le_add_iff_left, le_add_iff_nonneg_right, zero_le]

@[simp]
lemma removedHeap_of_singleton_union {heap : Heap} (h : l' < l ∨ l+n ≤ l') :
    removedHeap (singleton l' q ∪ heap) l n = removedHeap heap l n := by
  apply funext
  intro l''
  simp only [removedHeap, Union.union, singleton]
  split_ifs
  case pos h_l h_l'' =>
    exfalso
    obtain rfl := h_l''
    cases h with
    | inl h_lt =>
      have := not_le_of_lt h_lt
      exact this h_l.left
    | inr h_lt =>
      have := not_le_of_lt h_l.right
      exact this h_lt
  case neg => rfl
  case neg => rfl

lemma removedHeap_of_removedHeap {heap : Heap} :
    removedHeap (removedHeap heap l n) l n = removedHeap heap l n := by
  apply funext
  intro l'
  simp only [removedHeap, ite_eq_left_iff]
  intro h
  rw [if_neg h]

lemma isAlloc_of_union_of_isAlloc {heap heap₁ heap₂ : Heap}
    (h_alloc : isAlloc heap₁ l n) (h_union : heap = heap₁ ∪ heap₂) :
    isAlloc heap l n := by
  intro l' h_le h_lt
  rw [h_union]
  specialize h_alloc l' h_le h_lt
  apply ne_undef_of_union_of_ne_undef
  exact h_alloc

lemma removedHeap_of_union {heap heap₁ heap₂ : Heap}
    (h_union : heap = heap₁ ∪ heap₂) (h_alloc : isAlloc heap₁ l n) :
    removedHeap heap₁ l n = removedHeap heap l n := by
  apply funext
  intro l'
  simp only [removedHeap]
  rename isAlloc heap₁ l n => h_alloc₁
  split_ifs
  case pos h_l' =>
    specialize h_alloc₁ l' h_l'.left h_l'.right
    rw [h_union, union_val_iff_of_val h_alloc₁]
  case neg => rfl

lemma remainHeap_of_union_removeHeap {heap heap' : Heap}
    (h : heap = removedHeap heap l n ∪ heap') (h_disjoint : disjoint (removedHeap heap l n) heap') :
    heap' = freeLoc heap l n := by
  apply funext
  intro l'
  simp only [freeLoc]
  split
  case isTrue h_l' =>
    specialize h_disjoint l'
    simp only [removedHeap, h_l', and_self, ↓reduceIte] at h_disjoint
    cases h_disjoint with
    | inl h_heap =>
      rw [h, union_undef_iff_undef] at h_heap
      exact h_heap.right
    | inr h_heap' => exact h_heap'
  case isFalse h_l' =>
    have := congr_fun h l'
    simp only [Union.union, removedHeap, h_l', ↓reduceIte] at this
    exact this.symm



end free

section emptyHeap

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

end emptyHeap

section singleton

lemma singleton_eq : singleton l q l = q := by simp only [singleton, ↓reduceIte]

lemma singleton_eq_of_ne (h : l ≠ l') : singleton l q l' = undef := by
  simp only [singleton, h, ↓reduceIte]

lemma singleton_ne_emptyHeap : singleton l q ≠ ∅ := by
  intro h
  have := congrFun h l
  simp only [singleton, ↓reduceIte, emptyHeap, reduceCtorEq] at this

lemma disjoint_singleton_of_disjoint_alloc {l : ℕ+} {q : ℚ} {heap₁ heap₂ : Heap}
    (h_disjoint : disjoint heap₁ heap₂) (h_alloc : heap₂ l ≠ undef) :
    disjoint heap₁ (singleton l q) := by
  intro l'
  cases h_disjoint l' with
  | inl h₁ => exact Or.inl h₁
  | inr h₂ =>
    cases eq_or_ne l' l with
    | inl h_eq =>
      exfalso
      rw [h_eq] at h₂
      exact h_alloc h₂
    | inr h_ne =>
      apply Or.inr
      simp only [singleton, ite_eq_right_iff, reduceCtorEq, imp_false]
      exact h_ne.symm

lemma disjoint_singleton_of_disjoint_singleton {heap : Heap}
    (h : disjoint heap (singleton l q)) :
    disjoint heap (singleton l q') := by
  intro l'
  cases h l' with
  | inl h => exact Or.inl h
  | inr h =>
    apply Or.inr
    simp only [singleton, ite_eq_right_iff, imp_false]
    rintro rfl
    simp only [singleton, ↓reduceIte, reduceCtorEq] at h

lemma singleton_eq_iff {heap : Heap} :
    singleton l q = heap ↔ heap l = q ∧ ∀ l' ≠ l, heap l' = undef := by
  apply Iff.intro
  · intro h
    apply And.intro
    · rw [← congrFun h l]
      simp only [singleton, ↓reduceIte]
    · intro l' h_l
      rw [← congrFun h l']
      simp only [singleton, h_l.symm, ↓reduceIte]
  · intro ⟨h_def, h_undef⟩
    apply funext
    intro l'
    simp only [singleton]
    split
    case isTrue h_l => rw [← h_l, h_def]
    case isFalse h_l =>
      apply Eq.symm
      apply h_undef l'
      simp only [ne_eq, Eq.comm, h_l, not_false_eq_true]

lemma singleton_eq_singleton_iff_eq :
    singleton l q = singleton l q' ↔ q = q' := by
  apply Iff.intro
  · intro h
    have := congrFun h l
    simp only [singleton, ↓reduceIte, val.injEq] at this
    exact this
  · rintro rfl
    rfl

lemma singleton_union_of_neq {heap : Heap} (h : l ≠ l') :
    (singleton l q ∪ heap) l' = heap l' := by
  rw [union_eq_of_left_undef]
  rw [singleton_eq_of_ne h]

lemma singleton_union {heap : Heap} :
    (singleton l q ∪ heap) l = q := by
  simp only [Union.union, singleton, ↓reduceIte]

lemma substituteLoc_singleton_eq :
    substituteLoc (singleton l q) l q' = (singleton l q') := by
  apply funext
  intro l'
  simp only [substituteLoc]
  split
  case isTrue h_l =>
    simp only [singleton, if_pos h_l]
  case isFalse h_l =>
    simp only [singleton, if_neg h_l]

lemma subsituteLoc_eq_union_singleton {heap : Heap} (h : heap l = undef) :
    substituteLoc heap l q = heap ∪ (singleton l q) := by
  apply funext
  intro l'
  rw [substituteLoc]
  split_ifs
  case pos h_eq =>
    obtain rfl := h_eq
    simp only [union_eq_of_left_undef h, singleton, ↓reduceIte]
  case neg h_ne =>
    rw [union_eq_of_right_undef]
    simp only [singleton, h_ne, ↓reduceIte]

theorem bigSingleton_eq_undef_iff (l : PNat) (n : ℕ) (qs : ℕ → ℚ) (l' : PNat) :
    bigSingleton l n qs l' = undef ↔ l' < l ∨ l+n ≤ l' := by
  simp only [bigSingleton, ite_eq_right_iff, reduceCtorEq, imp_false, not_and, not_lt]
  apply Iff.intro
  · intro h
    cases le_or_lt l l'
    case inl h_l => right; exact h h_l
    case inr h_l => left; exact h_l
  · rintro (h|h)
    · intro h'; exfalso; exact h'.not_lt h
    · intro _;  exact h

theorem bigSingleton_of_zero :
    bigSingleton l 0 qs = ∅ := by
  apply funext
  intro l'
  simp only [bigSingleton, add_zero, PNat.coe_lt_coe, emptyHeap, ite_eq_right_iff, reduceCtorEq,
    imp_false, not_and, not_lt, imp_self]

lemma disjoint_bigSingleton_of_isNotAlloc {heap : Heap} (h : isNotAlloc heap l n) :
    disjoint heap (bigSingleton l n qs) := by
  intro l'
  by_cases l ≤ l' ∧ l' < l+n
  case pos h_l' =>
    exact Or.inl <| h l' h_l'.left h_l'.right
  case neg h_l' =>
    simp only [not_and_or, not_le, not_lt] at h_l'
    apply Or.inr
    rw [bigSingleton_eq_undef_iff]
    exact h_l'

lemma disjoint_singleton_bigSingleton (h : l+n ≤ l') :
    disjoint (singleton l' q) (bigSingleton l n qs) := by
  intro l''
  cases eq_or_ne l' l'' with
  | inl h_eq =>
    apply Or.inr
    rw [bigSingleton_eq_undef_iff]
    apply Or.inr
    rw [← h_eq]
    exact h
  | inr h_ne =>
    apply Or.inl
    simp only [singleton, h_ne, ↓reduceIte]

lemma union_singleton_bigSingle :
    (bigSingleton l n qs) ∪ (singleton ⟨l+n,PNat.add_right_nat⟩ (qs n))
    = bigSingleton l (n+1) qs := by
  apply funext
  intro l'
  simp only [Union.union, bigSingleton, singleton]
  split
  case h_1 q h_q =>
    rw [← h_q]
    split
    case isTrue h_l' =>
      obtain ⟨h_le, h_lt⟩ := h_l'
      rw [if_pos]
      apply And.intro h_le
      apply lt_trans h_lt
      simp only [add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one]
    case isFalse h_l' =>
      simp only [if_neg h_l', reduceCtorEq] at h_q
  case h_2 q h_q =>
    split
    case isTrue h_l =>
      rw [if_pos]
      · simp only [← h_l, PNat.mk_coe, add_tsub_cancel_left]
      · simp only [← h_l, PNat.mk_coe, add_lt_add_iff_left, lt_add_iff_pos_right, zero_lt_one,
          and_true]
        rw [← Subtype.coe_le_coe]; nth_rw 2 [Subtype.coe_mk]
        exact Nat.le_add_right (↑l) n
    case isFalse h_l =>
      split
      case isTrue h_l' =>
        rw [if_pos] at h_q
        · simp only [reduceCtorEq] at h_q
        · apply And.intro h_l'.left
          have := Nat.le_of_lt_succ h_l'.right
          apply lt_of_le_of_ne this
          simp only [Nat.add_eq, ne_eq]
          rw [← Subtype.val_inj, Subtype.coe_mk] at h_l
          exact Ne.symm h_l
      case isFalse => rfl

lemma union_bigSingleton_eq_allocateLoc {heap : Heap} (h : isNotAlloc heap l n) :
    heap ∪ (bigSingleton l n 0) = allocateLoc heap l n := by
  apply funext
  intro l'
  simp only [allocateLoc]
  split_ifs
  case pos h_l' =>
    simp only [Union.union]
    specialize h l' h_l'.left h_l'.right
    simp only [h, bigSingleton, h_l', and_self, ↓reduceIte, Pi.zero_apply]
  case neg h_l' =>
    simp only [Union.union]
    split
    case h_1 q h_q => exact h_q.symm
    case h_2 q h_q =>
      simp only [bigSingleton, Pi.zero_apply, if_neg h_l']
      exact h_q.symm


end singleton

section subset

instance : HasSubset Heap where
  Subset := subset

instance : PartialOrder Heap where
  le := subset
  le_refl heap := by use ∅, disjoint_emptyHeap', union_emptyHeap'.symm
  le_trans heap₁ heap₂ heap₃ := by {
    intro h₁₂ h₂₃
    obtain ⟨heap₁₂, h_disjoint₁₂, h_union₁₂⟩ := h₁₂
    obtain ⟨heap₂₃, h_disjoint₂₃, h_union₂₃⟩ := h₂₃
    use (heap₁₂ ∪ heap₂₃)
    constructor
    · rw [disjoint_union_iff]
      use h_disjoint₁₂
      rw [h_union₁₂, disjoint_comm, disjoint_union_iff, disjoint_comm] at h_disjoint₂₃
      exact h_disjoint₂₃.left
    · rw [h_union₂₃, h_union₁₂, union_assoc]
  }
  le_antisymm heap₁ heap₂ := by {
    intro h₁₂ h₂₁
    obtain ⟨heap₁₂, _, h_union₁₂⟩ := h₁₂
    obtain ⟨heap₂₁, _, h_union₂₁⟩ := h₂₁
    apply eq_of_union_of_union h_union₂₁ h_union₁₂
  }

theorem subset_of_union {heap heap₁ heap₂ : Heap}
    (h_disjoint : disjoint heap₁ heap₂) (h_union : heap = heap₁ ∪ heap₂) :
    heap₁ ⊆ heap := by
  use heap₂

theorem heap_def_of_subset {heap heap' : Heap} (h_subset : heap' ⊆ heap)
    {l : ℕ+} {q : ℚ} (h : heap' l = q) : heap l = q := by
  obtain ⟨heap'', _, h_union⟩ := h_subset
  rw [h_union]
  exact union_val_of_val h

theorem disjoint_heapminus (heap heap' : Heap) :
    disjoint heap' (heapminus heap heap') := by
  intro l
  simp only [heapminus]
  split_ifs
  case pos h => left; rw [h]
  case neg h => right; rfl

theorem union_heapminus {heap heap' : Heap} (h_subset : heap' ⊆ heap) :
    heap = heap' ∪ heapminus heap heap' := by
  apply funext
  intro l
  rw [union_comm _ _ (disjoint_heapminus _ _)]
  simp only [Union.union, heapminus]
  split
  case h_1 q h =>
    split_ifs at h
    rw [h]
  case h_2 q h =>
    split_ifs at h
    case pos h' => rw [h, h']
    case neg h' =>
      rw [← ne_eq, neq_undef_iff_exists_val] at h'
      obtain ⟨q, h'⟩ := h'
      rw [h']
      exact heap_def_of_subset h_subset h'

theorem union_of_subset {heap heap' : Heap} (h_subset : heap' ⊆ heap) :
    ∃ heap'', disjoint heap' heap'' ∧ heap = heap' ∪ heap'' := by
  use heapminus heap heap', disjoint_heapminus _ _, union_heapminus h_subset



end subset

end State
