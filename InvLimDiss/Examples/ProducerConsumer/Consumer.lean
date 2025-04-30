import InvLimDiss.Examples.ProducerConsumer.Basic

open Syntax CFSL FSL SL

theorem consumer_sound₁ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (var "y3") ⦄
    "x3" ≔* add (var "z2") (var "y3")
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
      ⊓ ((var "x3" === const 0) ⊔ (var "x3" === const 1) ⊔ var "x3" === const 2) ⦄ := by
  apply safeTuple_atom
  · simp only [Atom.atomicProgram]
  apply safeTuple_monotonicty
    `[fsl| S (q : ℚ). add (var "z2") (var "y3") ↦ q ⋆ (add (var "z2") (var "y3") ↦ q
        -⋆ (((⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
        ⊓ ((var "x3" === const 0) ⊔ (var "x3" === const 1) ⊔ var "x3" === const 2))
        ⋆ [[rInv y]])("x3" ↦ q)))]
    _ ?_ le_rfl
  swap
  · sorry
  apply safeTuple_lookup
  rw [varRV_of_fslEmp]
  decide

theorem consumer_sound₂ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3")) ⦄
      "l" ≔ inc (var "l")
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (dec (var "y3")) ⦄ := by sorry

theorem consumer_sound₃ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (dec $ var "y3") ⦄
    "y3" ≔ dec (var "y3") ⦃
    ⁅is_in_ico "y3" (-1) ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (var "y3") ⦄ := by sorry

theorem consumer_sound (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")⦄
    consumer
    ⦃ var "l" === const ↑y ⦄ := by
  unfold consumer
  apply safeTuple_monotonicty _
    `[fsl| ⁅is_in_ico "y3" (-1) y⁆
      ⬝ var "y3" === const (-1) ⬝ var "l" === sub (dec $ const y) (var "y3")] le_rfl
  · simp only [conservative_mul, conservative_equals]
    rw [conservative_entail]
    intro s ⟨h_ico, h_y3, h_l⟩
    simp only [slEquals, var, const]
    simp only [slEquals, var, sub, dec, const] at h_l
    simp only [slEquals, var, const] at h_y3
    rw [h_l, h_y3]
    simp only [sub_neg_eq_add, sub_add_cancel]
  apply safeTuple_while `[fsl| ⁅is_in_ico "y3" 0 y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")]
  swap
  · rw [is_in_ico_eq_or_first _ (Int.le.intro_sub (y + Nat.succ 0) rfl)]
    simp only [Int.reduceNeg, neg_add_cancel, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [← conservative_max, fslMin_fslMax_right]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslMax
      left
      simp only [conservative_equals, conservative_min, conservative_mul, conservative_entail]
      intro s ⟨h_ico, h_eq⟩
      simp only [slEquals, var, sub, dec, const] at h_eq
      apply And.intro
      · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop] at h_ico
        obtain ⟨i, ⟨h_iu, h_il⟩, h_i⟩ := h_ico
        simp only [slExp, leq, const, var, decide_eq_true_eq]
        rw [← h_i]
        norm_cast
      exact And.intro h_ico h_eq
    · apply le_fslMax
      right
      simp only [conservative_equals, conservative_min, conservative_not, conservative_max,
        conservative_mul, conservative_entail]
      intro s ⟨⟨h_y3, h_y⟩, h_l⟩
      apply And.intro
      · simp only [slNot, slExp, leq, const, var, decide_eq_true_eq, not_le]
        simp only [slEquals, var, const] at h_y3
        rw [h_y3]
        rfl
      apply And.intro
      · right
        exact ⟨h_y3, h_y⟩
      exact ⟨h_y3, h_l⟩
  apply safeTuple_seq _ (consumer_sound₁ y)
  apply safeTuple_monotonicty
    `[fsl|
      ⁅<eq (var "x3") (const 0)>⁆ ⬝ ⁅is_in_ico "y3" (-1) ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
      ⊔ ~⁅<eq (var "x3") (const 0)>⁆ ⬝ ⁅is_in_ico "y3" 0 y⁆ ⊓ (var "l" === sub (dec $ const y) (var "y3"))
        ⊓ ((var "x3" === const 1) ⊔ var "x3" === const 2)]
    _ ?_ le_rfl
  swap
  · sorry
  apply safeTuple_conditionalBranching (safeTuple_skip _ _)
  apply safeTuple_seq _ ?_ (consumer_sound₃ y)
  apply safeTuple_monotonicty
    `[fsl|
      ⁅<eq (var "x3") (const (-1))>⁆ ⬝ fFalse
      ⊔ ~⁅<eq (var "x3") (const (-1))>⁆ ⬝ ⁅is_in_ico "y3" 0 y⁆
        ⊓ (var "l" === sub (dec $ const y) (var "y3"))]
    _ ?_ le_rfl
  swap
  · sorry
  exact safeTuple_conditionalBranching safeTuple_false_left (consumer_sound₂ y)
