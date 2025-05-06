import InvLimDiss.CFSL
import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.Examples.SyntaxHelp
import InvLimDiss.SL.Framing.VarApprox

open Syntax

noncomputable def init (y : ℕ) : Program String :=
  [Prog| "l" ≔ const 0; "y1" ≔ dec $ const y; "y2" ≔ dec $ const y; "y3" ≔ dec $ const y]

noncomputable def producer : Program String :=
  [Prog| while leq (const 0) (var "y1") begin
    pif half then "x1" ≔ (const 1) else "x1" ≔ (const 2) fi;
    add (var "z1") (var "y1") *≔ (var "x1");
    "y1" ≔ dec <| var "y1"
  fi]

noncomputable def channel (p : unitInterval) : Program String :=
  [Prog| while leq (const 0) (var "y2") begin
    "x2" ≔* add (var "z1") (var "y2");
    if eq (var "x2") (const 0) then
      skip
    else
      pif constP p then
        add (var "z2") (var "y2") *≔ var "x2"
      else
        add (var "z2") (var "y2") *≔ const (-1)
      fi;
      "y2" ≔ dec <| var "y2"
    fi
  fi]

noncomputable def consumer : Program String :=
  [Prog| while leq (const 0) (var "y3") begin
    "x3" ≔* add (var "z2") (var "y3");
    if eq (var "x3") (const 0) then
      skip
    else
      if eq (var "x3") (const (-1)) then
        skip
      else
        "l" ≔ inc (var "l")
      fi;
      "y3" ≔ dec <| var "y3"
    fi
  fi]

noncomputable def producerConsumer (y : ℕ) (p : unitInterval) : Program String :=
  [Prog| [[init y]]; ([[producer]] || [[channel p]] || [[consumer]])]


open CFSL FSL SL

noncomputable def is_in_ico (v : String) (lower upper : ℤ) : StateProp String :=
  `[sl| ∃ (i : Set.Ico lower upper). const i === var v]

theorem substProp_ico_neq {v v' : String} (h : v ≠ v') :
    substProp (is_in_ico v l u) v' e = is_in_ico v l u := by
  funext s
  rw [← iff_eq_eq]
  apply Iff.intro
  · intro h_ico
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, Subtype.exists,
      Set.mem_Ico, exists_prop] at h_ico
    obtain ⟨i, h_bound, h_eq⟩ := h_ico
    simp only [is_in_ico, slExists_apply, Subtype.exists, Set.mem_Ico, exists_prop]
    use i, h_bound
    simp only [slEquals, const, var, State.substituteVar, if_neg h.symm] at h_eq
    exact h_eq
  · intro h_ico
    simp only [is_in_ico, slExists_apply, Subtype.exists, Set.mem_Ico, exists_prop] at h_ico
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, Subtype.exists,
      Set.mem_Ico, exists_prop]
    obtain ⟨i, h_bound, h_eq⟩ := h_ico
    use i, h_bound
    simp only [slEquals, const, var] at h_eq
    simp only [slEquals, const, var, State.substituteVar, if_neg h.symm]
    exact h_eq

theorem substProp_ico_eq_dec_upper (v : String) (l : ℤ) (u : ℕ) (h : l < u) :
    substProp (is_in_ico v l u) v (dec $ const u) = slTrue := by
  funext
  rw [← iff_eq_eq]
  apply Iff.intro
  · exact fun a ↦ rfl
  · intro _
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, slEquals, const, var,
      State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico, exists_prop]
    use u-1
    simp only [sub_lt_self_iff, zero_lt_one, and_true, Int.cast_sub, Int.cast_one]
    apply And.intro
    · exact Int.le_sub_one_of_lt h
    · rfl

theorem substProp_ico_dec_var (v : String) (y : ℕ):
    substProp (is_in_ico v (-1) ↑y) v (dec (var v))
    = is_in_ico v 0 ↑(y+1) := by
  funext s
  rw [← iff_eq_eq]
  apply Iff.intro
  · intro h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico,
      exists_prop] at h
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop]
    use i+1
    apply And.intro
    · apply And.intro
      · rw [Int.le_add_iff_sub_le, zero_sub]
        exact h_l
      · rw [add_lt_add_iff_right]
        exact h_u
    · rw [Int.cast_add, Int.cast_one, h_eq, sub_add_cancel]
  · intro h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop] at h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico, exists_prop]
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    use i-1
    apply And.intro
    · apply And.intro
      · rw [neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
        exact h_l
      · rw [Int.sub_lt_iff]
        exact h_u
    · rw [Int.cast_sub, Int.cast_one, sub_left_inj]
      exact h_eq

theorem substProp_ico_dec_var' (v : String) (y : ℕ):
    substProp (is_in_ico v 0 ↑y) v (dec (var v))
    = is_in_ico v 1 ↑(y+1) := by
  funext s
  rw [← iff_eq_eq]
  apply Iff.intro
  · intro h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico,
      exists_prop] at h
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop]
    use i+1
    apply And.intro
    · apply And.intro
      · rw [Int.le_add_iff_sub_le, sub_self]
        exact h_l
      · rw [add_lt_add_iff_right]
        exact h_u
    · rw [Int.cast_add, Int.cast_one, h_eq, sub_add_cancel]
  · intro h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop] at h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico, exists_prop]
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    use i-1
    apply And.intro
    · apply And.intro
      · rw [sub_nonneg]
        exact h_l
      · rw [Int.sub_lt_iff]
        exact h_u
    · rw [Int.cast_sub, Int.cast_one, sub_left_inj]
      exact h_eq

theorem is_in_ico_le_up (v : String) (l : ℤ) {y y' : ℤ} (h : y ≤ y') :
    (is_in_ico v l y) ⊢ (is_in_ico v l y') := by
  intro s h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop] at h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop]
  obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
  use i
  apply And.intro ?_ h_eq
  apply And.intro h_l
  exact lt_of_lt_of_le h_u h

theorem is_in_ico_le_down (v : String) (l l' : ℤ) {u : ℤ} (h : l ≤ l') :
    (is_in_ico v l' u) ⊢ (is_in_ico v l u) := by
  intro s h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop] at h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop]
  obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
  use i
  apply And.intro ?_ h_eq
  apply And.intro ?_ h_u
  apply le_trans h h_l

theorem is_in_ico_eq_or_last (v : String) {l u : ℤ} (h : l ≤ u) :
    is_in_ico v l (u+1) = `[sl| [[is_in_ico v l u]] ∨ (var v === const u)] := by
  funext s
  rw [slOr, Pi.sup_apply]
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop, sup_Prop_eq, eq_iff_iff]
  apply Iff.intro
  · rintro ⟨i, ⟨h_l, h_u⟩, h_eq⟩
    rw [Int.lt_add_one_iff, Int.le_iff_lt_or_eq] at h_u
    cases h_u
    case inl h_u =>
      left
      use i
    case inr h_u =>
      right
      qify at h_u
      rw [← h_u, h_eq]
  · rintro (⟨i, ⟨h_l, h_u⟩, h_eq⟩ | h_eq)
    · use i
      apply And.intro ?_ h_eq
      apply And.intro h_l
      apply lt_trans h_u
      exact Int.lt_succ u
    · use u
      apply And.intro ?_ h_eq.symm
      apply And.intro h
      exact Int.lt_succ u

theorem is_in_ico_le_or_first (v : String) {l u : ℤ}:
    is_in_ico v l u ≤ `[sl| [[is_in_ico v (l+1) u]] ∨ (var v === const l) ∧ ¬(const l === const u)] := by
  intro s h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop] at h_ico
  conv at h_ico => right; intro i; rw [le_iff_lt_or_eq]
  obtain ⟨i, ⟨h_l | h_l, h_u⟩, h_eq⟩ := h_ico
  · left
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
      exists_prop]
    use i
    apply And.intro ?_ h_eq
    apply And.intro ?_ h_u
    exact h_l
  · right
    apply And.intro
    · simp only [slEquals, var, const]
      rw [h_l, h_eq]
    · simp only [slNot, slEquals, const, Int.cast_inj]
      intro h
      apply h_u.not_le
      rw [← h, h_l]

theorem is_in_ico_eq_or_first (v : String) {l u : ℤ} (h : l ≤ u) :
    is_in_ico v l u = `[sl| [[is_in_ico v (l+1) u]] ∨ (var v === const l) ∧ ¬(const l === const u)] := by
  apply le_antisymm
  · exact is_in_ico_le_or_first v
  · rintro s (h_ico | ⟨h_eq, h_neq⟩)
    · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
        exists_prop] at h_ico
      obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
      simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
        exists_prop]
      use i
      apply And.intro ?_ h_eq
      apply And.intro ?_ h_u
      apply le_trans ?_ h_l
      exact Int.le.intro 1 rfl
    · simp only [slEquals, var, const] at h_eq
      simp only [slNot, slEquals, const, Int.cast_inj] at h_neq
      simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
        exists_prop]
      use l
      apply And.intro ?_ h_eq.symm
      apply And.intro le_rfl
      apply lt_of_le_of_ne h h_neq

theorem pure_is_in_ico (v : String) (l u : ℤ) :
    pure `[fsl| ⁅is_in_ico v l u⁆] := by
  intro s heap₁ heap₂
  simp only [fslIverson, is_in_ico, slExists_apply, slEquals, Subtype.exists, Set.mem_Ico,
    exists_prop]

theorem slExp_leq_fslBigSepMul_le_fslBigSepMul_cases {n : ℕ} {f : ℕ → StateRV String} :
    `[fsl| (⁅<leq (const n) (var v)>⁆) ⊓ [⋆] i ∈ { ... n }. [[f i]] ] ⊢
    `[fsl| [⋆] i ∈ { ... n }. ((~var v === const ↑i) ⊓ [[f i]] ⊔ (var v === const ↑i) ⊓ emp) ] := by
  induction n
  case zero =>
    simp only [CharP.cast_eq_zero, fslBigSepMul]
    apply fslMin_le
    right
    exact le_rfl
  case succ n ih =>
    unfold fslBigSepMul
    simp only [Nat.cast_add, Nat.cast_one]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [← fslMin_self (`[fsl| ⁅<leq (const (n+1)) (var v)>⁆])]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul, ← fslMul_assoc]
    rw [fslSepMul_comm]
    rw [fslMul_fslSepMul_of_pure pure_fslIverson_slExp]
    rw [fslSepMul_comm]
    rw [fslMul_fslSepMul_of_pure pure_fslIverson_slExp]
    apply fslSepMul_mono
    · apply le_fslMax
      left
      rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
      apply fslMin_le_fslMin ?_ le_rfl
      intro s
      simp only [fslIverson, slExp, leq, const, var, decide_eq_true_eq, fslNot, fslEquals,
        unitInterval.sym_iteOneZero_eq, unitInterval.iteOneZero_le_iteOneZero]
      intro h_le h_eq
      rw [h_eq, add_le_iff_nonpos_right, ← not_lt] at h_le
      exact h_le rfl
    · apply le_trans ?_ ih
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      apply fslMul_mono ?_ le_rfl
      intro s
      simp only [fslIverson, unitInterval.iteOneZero_le_iteOneZero, slExp]
      exact leq_le_leq_succ n _

theorem fslEquals_fslBigSepMul_cases_le_fslBigSepMul (n : ℕ) (v : String) {f : ℕ → StateRV String} :
    `[fsl| ⁅<leq (const ↑n) (var v)>⁆ ⬝ [⋆] i ∈ { ... n }.
      (~(var v === const ↑i) ⊓ [[f i]] ⊔ (var v === const ↑i) ⊓ emp) ]
    ⊢ `[fsl| [⋆] i ∈ { ... n }. [[f i]] ] := by
  induction n
  case zero =>
    simp only [CharP.cast_eq_zero, fslBigSepMul]
    rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
    apply fslMin_le
    right
    exact le_rfl
  case succ n ih =>
    unfold fslBigSepMul
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← fslMin_self (`[fsl| ⁅<leq (const (n+1)) (var v)>⁆])]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul, ← fslMul_assoc]
    rw [fslSepMul_comm]
    rw [fslMul_fslSepMul_of_pure pure_fslIverson_slExp]
    rw [fslSepMul_comm]
    rw [fslMul_fslSepMul_of_pure pure_fslIverson_slExp]
    apply fslSepMul_mono
    · rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMin_comm, fslMin_fslMax_right]
      rw [entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply fslMin_le
        left
        apply fslMin_le
        right
        exact le_rfl
      · intro s
        rw [fslMin, Pi.inf_apply, inf_le_iff]
        by_cases h : (s.stack v = n)
        case pos =>
          right
          simp only [fslIverson, slExp, leq, const, var, h, add_le_iff_nonpos_right,
            decide_eq_true_eq]
          rw [unitInterval.iteOneZero_neg]
          · exact unitInterval.nonneg'
          · simp only [not_le, zero_lt_one]
        case neg =>
          left
          rw [fslMin, Pi.inf_apply, inf_le_iff]
          left
          simp only [fslEquals, var, const]
          rw [unitInterval.iteOneZero_neg h]
          exact unitInterval.nonneg'
    · apply le_trans ?_ ih
      apply fslMul_mono ?_ le_rfl
      intro s
      simp only [fslIverson, slExp, unitInterval.iteOneZero_le_iteOneZero]
      exact leq_le_leq_succ n _

theorem fslEquals_le_slExp_leq (n : ℕ) (v : String) :
    `[fsl| ⁅var v === const ↑n⁆ ] ⊢ `[fsl| ⁅<leq (const ↑n) (var v)>⁆ ] := by
  intro s
  simp only [fslIverson, slEquals, var, const, slExp, leq, decide_eq_true_eq,
    unitInterval.iteOneZero_le_iteOneZero]
  intro h
  rw [h]

theorem ico_fslBigSepMul (n : ℕ) (v : String) {f : ℕ → StateRV String} :
    `[fsl| ⁅is_in_ico v 0 n⁆ ⊓ [⋆] i ∈ { ... n}. [[f i]]]
    = `[fsl| ⁅is_in_ico v 0 n⁆ ⊓ (S (j : ℕ). (var v === const ↑j) ⊓ [[f j]])
      ⋆ [⋆] i ∈ { ... n}. (~(var v === const i) ⊓ [[f i]] ⊔ (var v === const i) ⊓ emp)] := by
  induction n
  case zero =>
    funext s
    simp only [fslMin, is_in_ico, Int.cast_ofNat_Int]
    rw [Pi.inf_apply, Pi.inf_apply]
    simp only [fslIverson, slExists_apply, lt_self_iff_false, not_false_eq_true, Set.Ico_eq_empty,
      Set.isEmpty_coe_sort, IsEmpty.exists_iff, unitInterval.iteOneZero_false, zero_le,
      inf_of_le_left]
  case succ n ih =>
    unfold fslBigSepMul
    simp only [Nat.cast_add, Nat.cast_one]
    rw [is_in_ico_eq_or_last _ (Int.ofNat_zero_le n), ← conservative_max, fslMin_fslMax_right, fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [fslSepMul_comm, fslMul_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
    rw [← fslIverson_fslMin_eq_fslIverson_fslMul, ih]
    rw [fslMin_fslMax_right]
    apply le_antisymm
    · rw [fslMax_le_iff]
      apply And.intro
      · apply le_fslMax
        left
        rw [fslIverson_fslMin_eq_fslIverson_fslMul, ← fslMul_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
        nth_rw 1 [← fslMin_self (`[fsl| ⁅is_in_ico v 0 n⁆])]
        rw [fslMin_assoc]
        apply fslMin_le_fslMin le_rfl
        rw [fslSepMul_comm]
        rw [fslIverson_fslMin_eq_fslIverson_fslMul, fslMul_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [fslSepMul_comm, ← fslSepMul_assoc]
        apply fslSepMul_mono le_rfl
        rw [fslSepMul_comm]
        apply fslSepMul_mono ?_ le_rfl
        rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
        apply le_fslMax
        left
        apply fslMin_le_fslMin ?_ le_rfl
        intro s
        simp only [fslIverson, is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists,
          Set.mem_Ico, exists_prop, fslNot, fslEquals, unitInterval.sym_iteOneZero_eq,
          unitInterval.iteOneZero_le_iteOneZero, forall_exists_index, and_imp]
        intro i h_l h_u h_eq h_eq_n
        qify at h_u
        rw [h_eq, h_eq_n] at h_u
        simp only [lt_self_iff_false] at h_u
      · apply le_fslMax
        right
        rw [entailment_iff_pi_le, le_fslMin_iff]
        apply And.intro
        · apply fslMin_le
          left
          exact le_rfl
        · simp only [Int.cast_natCast]
          rw [← fslMin_self (`[fsl| ⁅var v === const n⁆]), fslMin_assoc]
          rw [fslIverson_fslMin_eq_fslIverson_fslMul, fslIverson_fslMin_eq_fslIverson_fslMul]
          simp only [← conservative_equals]
          rw [fslMul_fslSepMul_of_pure pure_fslEquals]
          rw [fslSepMul_comm]
          rw [fslMul_fslSepMul_of_pure pure_fslEquals]
          apply fslSepMul_mono
          · rw [conservative_equals, ← fslIverson_fslMin_eq_fslIverson_fslMul, ← conservative_equals]
            apply le_fslSup _ _ n
            exact le_rfl
          · nth_rw 1 [conservative_equals, ← fslMin_self (`[fsl| ⁅var v === const n⁆])]
            rw [fslIverson_fslMin_eq_fslIverson_fslMul, ← fslMul_assoc]
            rw [← conservative_equals]
            rw [fslMul_eq_emp_fslSepMul_of_pure pure_fslEquals]
            apply fslSepMul_mono
            · apply le_fslMax
              right
              exact le_rfl
            · rw [conservative_equals, ← fslIverson_fslMin_eq_fslIverson_fslMul]
              apply le_trans ?_ slExp_leq_fslBigSepMul_le_fslBigSepMul_cases
              apply fslMin_le_fslMin ?_ le_rfl
              exact fslEquals_le_slExp_leq n v
    · rw [fslMax_le_iff]
      apply And.intro
      · apply le_fslMax
        left
        rw [fslSepMul_comm, ← fslSepMul_assoc]
        nth_rw 1 [← fslMin_self `[fsl| ⁅is_in_ico v 0 n⁆], fslMin_assoc]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [fslSepMul_comm]
        rw [fslIverson_fslMin_eq_fslIverson_fslMul,
          fslMul_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [fslSepMul_comm]
        nth_rw 3 [fslSepMul_comm]
        apply fslSepMul_mono
        · rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [fslMin_comm, fslMin_fslMax_right]
          rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · apply fslMin_le
            left
            apply fslMin_le
            right
            exact le_rfl
          · rw [fslMin_comm, ← fslMin_assoc]
            apply fslMin_le
            left
            intro s
            rw [fslMin, Pi.inf_apply]
            simp only [fslIverson, is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists,
              Set.mem_Ico, exists_prop, fslEquals, unitInterval.iteOneZero_eq_ite]
            split_ifs
            case pos h h_eq =>
              exfalso
              obtain ⟨i, ⟨h_l, h_u⟩, h_eq'⟩ := h
              qify at h_u
              rw [h_eq', h_eq] at h_u
              simp only [lt_self_iff_false] at h_u
            case _ => simp only [zero_le, inf_of_le_right]
            case pos => simp only [zero_le, inf_of_le_left]
            case neg => simp only [min_self, zero_le]
        · rw [fslSepMul_comm, fslIverson_fslMin_eq_fslIverson_fslMul]
          exact le_rfl
      · apply le_fslMax
        right
        simp only [Int.cast_natCast]
        rw [fslSepMul_comm, ← fslSepMul_assoc]
        nth_rw 1 [← fslMin_self `[fsl| ⁅var v === const n⁆], fslMin_assoc]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_fslSepMul_of_pure pure_fslIverson_slEquals]
        rw [fslSepMul_comm]
        rw [fslIverson_fslMin_eq_fslIverson_fslMul,
          fslMul_fslSepMul_of_pure pure_fslIverson_slEquals]
        rw [fslSepMul_comm]
        nth_rw 3 [← fslSepMul_fslEmp_eq (fslMin _ _)]
        nth_rw 3 [fslSepMul_comm]
        apply fslSepMul_mono
        · rw [← fslIverson_fslMin_eq_fslIverson_fslMul, fslMin_comm]
          rw [fslMin_fslMax_right]
          rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · rw [fslMin_comm, ← fslMin_assoc]
            apply fslMin_le
            left
            rw [conservative_equals, conservative_not, conservative_min]
            intro s
            rw [fslIverson, slAnd, Pi.inf_apply, slEquals, slNot, slEquals,
              unitInterval.iteOneZero_le]
            rintro ⟨h, hn⟩
            exfalso
            exact hn h
          · apply fslMin_le
            left
            apply fslMin_le
            right
            exact le_rfl
        · rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
          nth_rw 1 [← fslMin_self (`[fsl| ⁅var v === const n⁆])]
          rw [fslMin_assoc]
          apply fslMin_le_fslMin le_rfl
          nth_rw 1 [← fslMin_self (`[fsl| ⁅var v === const n⁆])]
          rw [fslMin_assoc]
          rw [fslIverson_fslMin_eq_fslIverson_fslMul, fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [fslMul_fslSepMul_of_pure pure_fslIverson_slEquals]
          rw [fslSepMul_comm]
          rw [fslMul_fslSepMul_of_pure pure_fslIverson_slEquals]
          rw [fslSepMul_comm]
          apply fslSepMul_mono
          · apply le_trans ?_ (fslEquals_fslBigSepMul_cases_le_fslBigSepMul n v)
            apply fslMul_mono ?_ le_rfl
            exact fslEquals_le_slExp_leq n v
          · rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
            intro s
            rw [fslMin, Pi.inf_apply, inf_le_iff]
            by_cases h : s.stack v = n
            case pos =>
              right
              rw [fslSup, iSup_apply]
              apply iSup_le
              intro n'
              rw [fslMin, Pi.inf_apply, fslEquals, var, const]
              rw [inf_le_iff]
              by_cases h_n : n = n'
              case pos =>
                right
                rw [h_n]
              case neg =>
                left
                rw [unitInterval.iteOneZero_le]
                intro h'
                exfalso
                apply h_n
                qify
                rw [← h, ← h']
            case neg =>
              left
              simp only [fslIverson, slEquals, var, const]
              rw [unitInterval.iteOneZero_neg h]
              exact unitInterval.nonneg'

theorem neg_one_le_nat (n : ℕ) : (-1 : ℤ) < n := by
  apply lt_of_lt_of_le
  · apply Int.neg_neg_of_pos
    exact Int.zero_lt_one
  · exact Int.ofNat_zero_le n

noncomputable def rInv1 (y : ℕ) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. ((add (var "z1") (const i) ↦ const 0)
                          ⊔ (add (var "z1") (const i) ↦ const 1)
                          ⊔ (add (var "z1") (const i) ↦ const 2))]

noncomputable def rInv1_wo (y : ℕ) (v : String) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. (~(var v === const i) ⊓
                               ((add (var "z1") (const i) ↦ const 0)
                              ⊔ (add (var "z1") (const i) ↦ const 1)
                              ⊔ (add (var "z1") (const i) ↦ const 2))
                            ⊔ (var v === const i) ⊓ emp)]

noncomputable def rInv2 (y : ℕ) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. ((add (var "z2") (const i) ↦ const 0)
                          ⊔ (add (var "z2") (const i) ↦ const 1)
                          ⊔ (add (var "z2") (const i) ↦ const 2))]

noncomputable def rInv2_wo (y : ℕ) (v : String) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. (~(var v === const i) ⊓
                               ((add (var "z2") (const i) ↦ const 0)
                              ⊔ (add (var "z2") (const i) ↦ const 1)
                              ⊔ (add (var "z2") (const i) ↦ const 2))
                            ⊔ (var v === const i) ⊓ emp)]

noncomputable def rInv (y : ℕ) : StateRV String :=
  `[fsl| [[rInv1 y]] ⋆ [[rInv2 y]]]

theorem rInv_subset : varRV (rInv y) ⊆ {"z1", "z2"} := by
  rw [rInv]
  apply subset_trans varRV_of_fslSepMul
  apply Set.union_subset
  · rw [rInv1]
    apply subset_trans varRV_of_fslBigSepMul
    intro a ⟨i, h_i, h⟩
    apply Set.mem_of_subset_of_mem ?_ h; clear h h_i
    apply subset_trans varRV_of_fslMax
    apply Set.union_subset
    · apply subset_trans varRV_of_fslPointsTo
      apply Set.union_subset
      · apply subset_trans varValue_of_add
        rw [varValue_of_var, varValue_of_const]
        simp only [Set.union_empty, Set.singleton_subset_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, String.reduceEq, or_false]
      · rw [varValue_of_const]
        exact Set.empty_subset {"z1", "z2"}
    · apply subset_trans varRV_of_fslMax
      apply Set.union_subset
      · apply subset_trans varRV_of_fslPointsTo
        apply Set.union_subset
        · apply subset_trans varValue_of_add
          rw [varValue_of_var, varValue_of_const]
          simp only [Set.union_empty, Set.singleton_subset_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff, String.reduceEq, or_false]
        · rw [varValue_of_const]
          exact Set.empty_subset {"z1", "z2"}
      · apply subset_trans varRV_of_fslPointsTo
        apply Set.union_subset
        · apply subset_trans varValue_of_add
          rw [varValue_of_var, varValue_of_const]
          simp only [Set.union_empty, Set.singleton_subset_iff, Set.mem_insert_iff,
            Set.mem_singleton_iff, String.reduceEq, or_false]
        · rw [varValue_of_const]
          exact Set.empty_subset {"z1", "z2"}
  · rw [rInv2]
    apply subset_trans varRV_of_fslBigSepMul
    intro a ⟨i, h_i, h⟩
    apply Set.mem_of_subset_of_mem ?_ h; clear h h_i
    apply subset_trans varRV_of_fslMax
    apply Set.union_subset
    · apply subset_trans varRV_of_fslPointsTo
      apply Set.union_subset
      · apply subset_trans varValue_of_add
        rw [varValue_of_var, varValue_of_const]
        simp only [Set.union_empty, Set.subset_insert]
      · rw [varValue_of_const]
        exact Set.empty_subset {"z1", "z2"}
    · apply subset_trans varRV_of_fslMax
      apply Set.union_subset
      · apply subset_trans varRV_of_fslPointsTo
        apply Set.union_subset
        · apply subset_trans varValue_of_add
          rw [varValue_of_var, varValue_of_const]
          simp only [Set.union_empty, Set.subset_insert]
        · rw [varValue_of_const]
          exact Set.empty_subset {"z1", "z2"}
      · apply subset_trans varRV_of_fslPointsTo
        apply Set.union_subset
        · apply subset_trans varValue_of_add
          rw [varValue_of_var, varValue_of_const]
          simp only [Set.union_empty, Set.subset_insert]
        · rw [varValue_of_const]
          exact Set.empty_subset {"z1", "z2"}
