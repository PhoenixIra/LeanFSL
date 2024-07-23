import InvLimDiss.Program.State.Defs


namespace State

open Rat Classical HeapValue

section substituteVar

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

end substituteVar

section substituteLoc

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

end substituteLoc

section removeLoc

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

end removeLoc

section allocate

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

end allocate

section free

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

end free

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
  simp only [h_undef, ne_eq, not_false_eq_true]


theorem substituteLoc_disjoint {heap₁ heap₂ : Heap} {l : PNat} {q : ℚ}
    (h : heap₁ l ≠ undef) : disjoint (substituteLoc heap₁ l q) heap₂ ↔ disjoint heap₁ heap₂ := by
  unfold substituteLoc
  apply Iff.intro
  · intro h_disjoint l'
    cases h_disjoint l' with
    | inl h_disjoint =>
      simp only at h_disjoint
      split at h_disjoint
      case isTrue _ => exfalso; exact h_disjoint
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
  rw [isNotAlloc_def] at h_notAlloc
  by_cases h_l' : l ≤ l' ∧ l' < l + m
  case pos => exact Or.inr <| h_notAlloc l' h_l'.left h_l'.right
  case neg =>
    cases h l' with
    | inr h => exact Or.inr h
    | inl h =>
      apply Or.inl
      simp only [not_and_or, not_le, not_lt] at h_l'
      rw [allocateLoc_heap.left l' h_l']
      exact h

theorem disjoint_freeLoc {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h : disjoint heap₁ heap₂) : disjoint (freeLoc heap₁ l m) heap₂ := by
  intro l'
  cases h l' with
  | inr h => exact Or.inr h
  | inl h =>
    apply Or.inl
    by_cases h_le : l ≤ l' ∧ l' < l + m
    case pos => exact freeLoc_heap.right l' h_le.left h_le.right
    case neg =>
      simp only [not_and_or, not_le, not_lt] at h_le
      rw [freeLoc_heap.left l' h_le]
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
    case isTrue _ => exfalso; exact h_eq
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
  have : heap₁ l ≠ undef := by rw [h]; simp only [ne_eq, not_false_eq_true]
  rw [union_val_iff_of_val this]
  exact h

theorem union_undef_iff_undef {heap₁ heap₂ : Heap} {l : PNat} :
    (heap₁ ∪ heap₂) l = undef ↔ heap₁ l = undef ∧ heap₂ l = undef := by
  simp only [Union.union]
  apply Iff.intro
  · intro h
    split at h
    case h_1 _ => simp only at h
    case h_2 h_l => use h_l
  · intro h
    split
    case h_1 h_l => rw [h_l] at h; simp only [false_and] at h
    case h_2 _ => exact h.right

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
    induction n with
    | zero => simp only [isNotAlloc, and_self]
    | succ n ih =>
      unfold isNotAlloc at h ⊢
      obtain ⟨h_undef, h⟩ := h
      specialize ih h
      rw [union_undef_iff_undef] at h_undef
      use ⟨h_undef.left, ih.left⟩, h_undef.right, ih.right
  · intro h
    induction n with
    | zero => simp only [isNotAlloc]
    | succ n ih =>
      unfold isNotAlloc at h ⊢
      obtain ⟨⟨h_undef₁, h₁⟩, h_undef₂, h₂⟩ := h
      specialize ih ⟨h₁, h₂⟩
      rw [union_undef_iff_undef]
      use ⟨h_undef₁, h_undef₂⟩

theorem allocateLoc_union {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ} :
    allocateLoc heap₁ l m ∪ heap₂ = allocateLoc (heap₁ ∪ heap₂) l m := by
  apply funext
  intro l'
  induction m with
  | zero => simp only [allocateLoc]
  | succ n ih =>
    conv => left; rw [Union.union, union]
    simp only [allocateLoc, substituteLoc]
    split
    case h_1 h_val =>
      split
      case isTrue h_l' => rw [if_pos h_l'] at h_val; exact h_val.symm
      case isFalse h_l' =>
        rw [if_neg h_l'] at h_val
        rw [← ih]
        simp only [Union.union]
        rw [h_val]
    case h_2 h_val =>
      split
      case isTrue h_l' => simp only [if_pos h_l'] at h_val
      case isFalse h_l' =>
        rw [if_neg h_l'] at h_val
        rw [← ih]
        simp only [Union.union]
        rw [h_val]

theorem isAlloc_union {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h : isAlloc heap₁ l m) : isAlloc (heap₁ ∪ heap₂) l m := by
  induction m with
  | zero => simp only [isAlloc]
  | succ n ih =>
    unfold isAlloc at h ⊢
    obtain ⟨⟨v, heap_v⟩, h_alloc⟩ := h
    apply And.intro
    · use v
      exact union_eq_of_left heap_v
    · exact ih h_alloc

theorem union_freeLoc {heap₁ heap₂ : Heap} {l : ℕ+} {m : ℕ}
    (h_alloc : isAlloc heap₁ l m) (h_disjoint : disjoint heap₁ heap₂) :
    (freeLoc heap₁ l m) ∪ heap₂ = freeLoc (heap₁ ∪ heap₂) l m := by
  apply funext
  intro l'
  by_cases h_le : l ≤ l' ∧ l' < l + m
  case pos =>
    rw [freeLoc_heap.right l' h_le.left h_le.right]
    simp only [Union.union]
    rw [freeLoc_heap.right l' h_le.left h_le.right]
    simp only
    rw [isAlloc_def] at h_alloc
    obtain ⟨x, h_x⟩ := h_alloc l' h_le.left h_le.right
    exact undef_of_disjoint_of_val h_disjoint h_x
  case neg =>
    simp only [not_and_or, not_le, not_lt] at h_le
    rw [freeLoc_heap.left l' h_le]
    simp only [Union.union]
    rw [freeLoc_heap.left l' h_le]



end union

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

lemma singleton_ne_emptyHeap : singleton l q ≠ ∅ := by
  intro h
  have := congrFun h l
  simp only [singleton, ↓reduceIte, emptyHeap] at this

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
      simp only [singleton, ite_eq_right_iff, imp_false]
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
    simp only [singleton, ↓reduceIte] at h

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


end singleton

end State
