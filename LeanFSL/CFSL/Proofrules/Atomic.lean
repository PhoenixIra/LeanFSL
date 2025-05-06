import LeanFSL.CFSL.WeakExpectation
import LeanFSL.SL.FuzzySubstSimp
import LeanFSL.CFSL.Step.Framing
import LeanFSL.SL.Conservativity
import LeanFSL.SL.ClassicalProofrules

/-!
  Proofrules for wrle with atomic programs as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CFSL

open FSL Syntax OrderHom unitInterval Atom Semantics

private theorem support_wrle_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : reachState Var =>
      programSmallStepSemantics c s a cs.prog cs.state
      * (`[fsl| (wrle [cs.prog] ([[P]] ⋆ [[resource]] | emp )) ⋆ emp ] cs.state))
    ⊆ { cs : reachState Var | cs.prog = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_fsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.prog
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrle_eq_of_abort, fslSepMul_fslEmp_eq, fslFalse] at h_fsl
      simp only [not_true_eq_false] at h_fsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.state

private theorem support_wrle'_of_atom {c : Program Var} (h_atom : atomicProgram c)
    (s : State Var) (P resource : StateRV Var) :
    Function.support (fun cs : reachState Var =>
      programSmallStepSemantics c s a cs.prog cs.state
      * (`[fsl| (wrle [cs.prog] ([[P]] | [[resource]] )) ⋆ [[resource]] ] cs.state))
    ⊆ { cs : reachState Var | cs.prog = [Prog| ↓]} := by
  intro cs h_cs
  simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq] at h_cs
  obtain ⟨h_sem, h_fsl⟩ := h_cs
  by_cases h_fin_cs : finalProgram cs.prog
  · rw [finalPrograms_iff_or] at h_fin_cs
    cases h_fin_cs with
    | inl h => exact h
    | inr h =>
      rw [h, wrle_eq_of_abort, fslSepMul_comm, fslSepMul_fslFalse_eq, fslFalse] at h_fsl
      simp only [not_true_eq_false] at h_fsl
  · exfalso
    exact h_sem <| semantics_eq_zero_of_atomProgram h_atom h_fin_cs s a cs.state

theorem wrle_atom (h : `[fsl| [[Q]] ⋆ [[resource]] ⊢ wrle [c] ([[P]] ⋆ [[resource]] | emp)])
    (h_atom : atomicProgram c) :
    `[fsl| [[Q]] ⊢ wrle [c] ([[P]] | [[resource]])] := by
  have := atomic_not_final h_atom
  rw [wrle_eq_of_not_final this, le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans h
  rw [wrle_eq_of_not_final this, fslEmp_fslSepDiv_eq, Pi.le_def]
  intro s
  simp only [step, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a h_a
  apply sInf_le
  use a, h_a
  rw[← tsum_subtype_eq_of_support_subset <| support_wrle_of_atom h_atom s P resource]
  rw[← tsum_subtype_eq_of_support_subset <| support_wrle'_of_atom h_atom s P resource]
  apply le_antisymm
  · apply Summable.tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (programSmallStepSemantics c s a cs.val.prog cs.val.state) 0 with
    | inl h_zero =>
      rw [h_zero]
      simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_nzero =>
      apply unit_mul_le_mul le_rfl
      have := cs.prop
      simp only [Set.mem_setOf_eq] at this
      rw [this, wrle_eq_of_term, wrle_eq_of_term, fslSepMul_fslEmp_eq]
  · apply Summable.tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (programSmallStepSemantics c s a cs.val.prog cs.val.state) 0 with
    | inl h_zero =>
      rw [h_zero]
      simp only [Set.Icc.coe_zero, zero_mul, le_refl]
    | inr h_nzero =>
      apply unit_mul_le_mul le_rfl
      have := cs.prop
      simp only [Set.mem_setOf_eq] at this
      rw [this, wrle_eq_of_term, wrle_eq_of_term, fslSepMul_fslEmp_eq]

theorem wrle_skip : `[fsl| [[P]] ⊢ wrle [skip] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le, Pi.le_def]
  intro s
  rw [step_skip, wrle_eq_of_term]

theorem wrle_assign (h : x ∉ varRV RI) :
    `[fsl| [[P]](x ↦ e) ⊢ wrle [x ≔ e] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le, Pi.le_def]
  intro s
  rw [step_assign, wrle_eq_of_term]
  have : `[fsl| [[P]] ⋆ [[RI]]]  (s.substituteStack x (e s.stack))
    = `[fsl| ([[P]] ⋆ [[RI]])(x ↦ e)] s := rfl
  rw [this, substituteStack_of_fslSepCon e h]

open HeapValue State

theorem wrle_mutate :
    `[fsl| (S (q : ℚ). e_loc ↦ q) ⋆ (e_loc ↦ e_val -⋆ [[P]])
          ⊢ wrle [e_loc *≔ e_val] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases ∃ l : ℕ+, e_loc s.stack = l ∧ s.heap l ≠ undef
    case pos h_alloc =>
      obtain ⟨l, h_loc, h_alloc⟩ := h_alloc
      rw [step_mutate s _ h_loc h_alloc, wrle_eq_of_term]
      simp only [State.substituteHeap]
      apply sSup_le
      rintro _ ⟨heap_remove, heap_remain, h_disjoint, h_union, rfl⟩
      rw [← unit_le_div_iff_mul_le, fslSup_apply, iSup_le_iff]
      intro q
      simp only [fslPointsTo, iteOneZero_le, forall_exists_index, and_imp]
      intro l' h_loc' h_val'
      simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_loc'
      rw [unit_le_div_iff_mul_le]
      simp only [one_mul]
      apply sInf_le_of_le
      · use (singleton l (e_val s.stack))
        apply And.intro
        · rw [h_loc'] at h_val'
          simp only
          rw [State.disjoint_comm] at h_disjoint
          apply disjoint_singleton_of_disjoint_alloc h_disjoint
          simp only [h_val', State.singleton, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
        · rfl
      · simp only [fslPointsTo]
        rw [iteOneZero_pos]
        · rw [unit_div_one, ← h_union, h_val', ← substituteLoc_union, h_loc',
            substituteLoc_singleton_eq, union_comm]
          apply disjoint_singleton_of_disjoint_singleton
          rw [h_val', h_loc', disjoint_comm _ _] at h_disjoint
          exact h_disjoint
        · use l, h_loc.symm
    case neg h_ne_alloc =>
      apply sSup_le
      rintro _ ⟨heap_remove, heap_remain, _, h_union, rfl⟩
      rw [← unit_le_div_iff_mul_le]
      rw [fslSup_apply, iSup_le_iff]
      intro q
      simp only [fslPointsTo, iteOneZero_le, forall_exists_index, and_imp]
      intro l h_loc h_val
      exfalso
      apply h_ne_alloc
      use l, h_loc.symm
      rw [← h_union, h_val]
      apply ne_undef_of_union_of_ne_undef
      simp only [State.singleton, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]


theorem wrle_lookup (h : v ∉ varRV RI) :
    `[fsl| S (q : ℚ). e_loc ↦ q ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ q))
          ⊢ wrle [v ≔* e_loc] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.singleton_inter_eq_empty]
    exact h
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases ∃ l : ℕ+, e_loc s.stack = l ∧ s.heap l ≠ undef
    case pos h_alloc =>
      obtain ⟨l, h_loc, h_alloc⟩ := h_alloc
      rw [neq_undef_iff_exists_val] at h_alloc
      obtain ⟨q, h_q⟩ := h_alloc
      rw [step_lookup s _ h_loc h_q, wrle_eq_of_term]
      simp only [substituteStack]
      rw [fslSup_apply, iSup_le_iff]
      intro q
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
      simp only [fslPointsTo, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
      split
      case isTrue h_l' =>
        obtain ⟨l', h_l', h_singleton⟩ := h_l'
        simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_l'
        obtain rfl := h_l'
        have h_singleton' := h_singleton
        rw [Eq.comm, singleton_eq_iff] at h_singleton'
        simp only [← congrFun h_union l', h_singleton'.left, ne_eq, reduceCtorEq, not_false_eq_true,
          union_val_iff_of_val, val.injEq] at h_q
        obtain rfl := h_q
        clear h_singleton'
        apply sInf_le
        use (State.singleton l' q)
        apply And.intro
        · simp only [← h_singleton, State.disjoint_comm, h_disjoint]
        · simp only [fslPointsTo]
          rw [iteOneZero_pos]
          · simp only [← h_union, fslSubst, substituteStack, ← h_singleton, unit_div_one]
            rw [union_comm _ _ h_disjoint]
          · use l', h_loc.symm
      case isFalse h_l' =>
        simp only [zero_le]
    case neg h_nalloc =>
      simp only [ne_eq, not_exists, not_and, not_not] at h_nalloc
      rw [fslSup_apply, iSup_le_iff]
      intro q
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
      simp only [fslPointsTo]
      rw [iteOneZero_neg]
      · simp only [zero_mul, zero_le]
      · simp only [not_exists, not_and]
        intro l h_l h_heap₁
        specialize h_nalloc l h_l.symm
        rw [← h_union, union_undef_iff_undef, h_heap₁] at h_nalloc
        simp only [State.singleton, ↓reduceIte, reduceCtorEq, false_and] at h_nalloc

theorem wrle_compareAndSet_true (h : v ∉ varRV RI) :
    `[fsl| e_loc ↦ e_val ⋆ (e_loc ↦ e_set -⋆ [[P]](v ↦ (1:ℚ)))
          ⊢ wrle [v ≔ cas(e_loc, e_val, e_set)] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.singleton_inter_eq_empty]
    exact h
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases ∃ l : ℕ+, e_loc s.stack = l ∧ s.heap l ≠ undef
    case pos h_alloc =>
      obtain ⟨l, h_loc, h_alloc⟩ := h_alloc
      rw [neq_undef_iff_exists_val] at h_alloc
      obtain ⟨q, h_q⟩ := h_alloc
      cases eq_or_ne q (e_val s.stack)
      case inl h_eq =>
        rw [h_eq] at h_q
        rw [step_cas_of_eq s _ h_loc h_q, wrle_eq_of_term]
        apply sSup_le
        rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
        simp only [fslPointsTo, substituteStack, substituteHeap]
        rw [← unit_le_div_iff_mul_le, iteOneZero_le, unit_le_div_iff_mul_le]
        rintro ⟨l', h_l', h_singleton⟩
        simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_l'
        obtain rfl := h_l'
        simp only [one_mul]
        apply sInf_le_of_le
        · use (singleton l' (e_set s.stack))
          apply And.intro
          · simp only
            rw [h_singleton, State.disjoint_comm] at h_disjoint
            exact disjoint_singleton_of_disjoint_singleton h_disjoint
          · rfl
        · simp only [fslPointsTo]
          rw [iteOneZero_pos]
          pick_goal 2
          · use l', h_loc.symm
          · simp only [fslSubst, substituteStack, unit_div_one]
            rw [← h_union, ← substituteLoc_union, h_singleton, substituteLoc_singleton_eq, union_comm]
            rw [h_singleton, State.disjoint_comm] at h_disjoint
            apply disjoint_singleton_of_disjoint_singleton
            exact h_disjoint
      case inr h_ne =>
        apply sSup_le
        rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
        simp only [fslPointsTo]
        rw [iteOneZero_neg]
        · simp only [zero_mul, zero_le]
        · simp only [not_exists, not_and]
          intro l' h_loc' h_heap₁
          simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_loc'
          obtain rfl := h_loc'
          have := congrFun h_heap₁ l'
          simp only [State.singleton, ↓reduceIte] at this
          rw [← h_union, union_val_iff_of_val (by simp [this]), this] at h_q
          simp only [val.injEq] at h_q
          exact h_ne h_q.symm
    case neg h_nalloc =>
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
      simp only [fslPointsTo]
      rw [iteOneZero_neg]
      · simp only [zero_mul, zero_le]
      · simp only [not_exists, not_and]
        rintro l h_loc h_singleton
        simp only [ne_eq, not_exists, not_and, not_not] at h_nalloc
        specialize h_nalloc l h_loc.symm
        rw [← h_union, union_undef_iff_undef, h_singleton] at h_nalloc
        simp only [State.singleton, ↓reduceIte, reduceCtorEq, false_and] at h_nalloc

theorem wrle_compareAndSet_false (h : v ∉ varRV RI) :
    `[fsl| S (q : ℚ). (e_loc ↦ q ⬝ ~(q === e_val)) ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ (0:ℚ)))
          ⊢ wrle [v ≔ cas(e_loc, e_val, e_set)] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.singleton_inter_eq_empty]
    exact h
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases ∃ l : ℕ+, e_loc s.stack = l ∧ s.heap l ≠ undef
    case pos h_alloc =>
      obtain ⟨l, h_loc, h_alloc⟩ := h_alloc
      rw [neq_undef_iff_exists_val] at h_alloc
      obtain ⟨q, h_q⟩ := h_alloc
      cases eq_or_ne q (e_val s.stack)
      case inl h_eq =>
        rw [fslSup_apply, iSup_le_iff]
        intro q
        apply sSup_le
        rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
        simp only [fslMul, fslPointsTo, fslNot, fslEquals, sym_iteOneZero_eq,
          iteOneZero_mul_iteOneZero_eq]
        rw [iteOneZero_neg]
        · simp only [zero_mul, zero_le]
        · simp only [not_and, Decidable.not_not, forall_exists_index, and_imp]
          rintro l' h_l' h_singleton
          simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_l'
          obtain rfl := h_l'
          rw [← h_eq]
          rw [Eq.comm, singleton_eq_iff] at h_singleton
          simp only [← h_union, h_singleton.left, ne_eq, reduceCtorEq, not_false_eq_true,
            union_val_iff_of_val, val.injEq] at h_q
          exact h_q
      case inr h_ne =>
        rw [step_cas_of_neq s _ h_loc (neq_undef_iff_exists_val.mpr ⟨q, h_q⟩) (by simp [h_q, h_ne])]
        rw [wrle_eq_of_term]
        rw [fslSup_apply, iSup_le_iff]
        intro q
        apply sSup_le
        rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
        simp only [fslMul, fslPointsTo, fslNot, fslEquals, sym_iteOneZero_eq,
          iteOneZero_mul_iteOneZero_eq]
        rw [iteOneZero_eq_ite]
        split_ifs
        case pos h_l =>
          obtain ⟨⟨l', h_l', h_singleton⟩, _⟩ := h_l
          simp only [h_loc, Nat.cast_inj, PNat.coe_inj] at h_l'
          obtain rfl := h_l'
          have h_alloc₁ := (singleton_eq_iff.mp (Eq.symm h_singleton)).left
          simp only [← h_union, union_val_of_val h_alloc₁, val.injEq] at h_q
          obtain rfl := h_q
          simp only [one_mul, substituteStack, ge_iff_le]
          apply sInf_le
          use (singleton l' q)
          apply And.intro
          · simp only
            rw [← h_singleton, State.disjoint_comm]
            exact h_disjoint
          · simp only [fslPointsTo]
            rw [iteOneZero_pos]
            · rw [fslSubst, ← h_singleton, ← h_union, union_comm _ _ h_disjoint]
              simp only [substituteStack, unit_div_one]
            · use l', h_loc.symm
        case neg => simp only [zero_mul, substituteStack, zero_le]
    case neg h_nalloc =>
      rw [fslSup_apply, iSup_le_iff]
      intro q
      apply sSup_le
      rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
      simp only [fslMul, fslPointsTo, fslNot, fslEquals, sym_iteOneZero_eq,
          iteOneZero_mul_iteOneZero_eq]
      rw [iteOneZero_neg]
      · simp only [zero_mul, zero_le]
      · simp only [not_and, Decidable.not_not, forall_exists_index, and_imp]
        rintro l h_loc h_singleton
        simp only [ne_eq, not_exists, not_and, not_not] at h_nalloc
        specialize h_nalloc l h_loc.symm
        rw [← h_union, union_undef_iff_undef, h_singleton] at h_nalloc
        simp only [State.singleton, ↓reduceIte, reduceCtorEq, false_and] at h_nalloc

theorem wrle_compareAndSet (h : v ∉ varRV RI) :
    `[fsl| (e_loc ↦ e_val ⋆ (e_loc ↦ e_set -⋆ [[P]](v ↦ (1:ℚ))))
      ⊔ (S (q : ℚ). (e_loc ↦ q ⬝ ~(q === e_val)) ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ (0:ℚ))))
          ⊢ wrle [v ≔ cas(e_loc, e_val, e_set)] ([[P]] | [[RI]])] := by
  rw [fslMax_le_iff]
  apply And.intro
  · exact wrle_compareAndSet_true h
  · exact wrle_compareAndSet_false h

theorem wrle_allocate (h : v ∉ varRV RI) :
    `[fsl| S (n : ℕ). e_len === (n : ℚ) ⬝ I (l : ℕ+).
          ([⋆] i ∈ { ... n}. (l+i : ℚ) ↦ (0:ℚ)) -⋆ [[P]](v ↦ (l:ℚ))
          ⊢ wrle [ [Prog| v ≔ alloc(e_len)] ] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.singleton_inter_eq_empty]
    exact h
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases ∃ n : ℕ, e_len s.stack = n
    case pos h =>
      obtain ⟨n, h_n⟩ := h
      rw [step_alloc s _ h_n]
      apply le_sInf
      rintro _ ⟨l, h_nalloc, rfl⟩
      rw [wrle_eq_of_term]
      rw [fslSup_apply, iSup_le_iff]
      intro n'
      simp only [fslMul, fslEquals, substituteStack, allocateHeap, iteOneZero_eq_ite]
      split
      case isFalse h_n' =>
        simp only [zero_mul, zero_le]
      case isTrue h_n' =>
        simp only [h_n, Nat.cast_inj] at h_n'
        obtain rfl := h_n'
        simp only [one_mul]
        rw [fslInf_apply]
        apply le_trans (iInf_le _ l)
        apply sInf_le
        use (bigSingleton l n 0), disjoint_bigSingleton_of_isNotAlloc h_nalloc
        rw [fslBigSepMul_of_fslPointsTo_of_bigSingleton_eq_one]
        simp only [unit_div_one, fslSubst, substituteStack]
        rw [union_bigSingleton_eq_allocateLoc h_nalloc]
    case neg h =>
      simp only [not_exists] at h
      rw [step_alloc_of_abort s _ h]
      apply iSup_le
      rintro ⟨_, n, rfl⟩
      simp only [fslMul, nonpos_iff_eq_zero, mul_eq_zero]
      apply Or.inl
      simp only [fslEquals, h n, iteOneZero_false]

theorem wrle_free :
    `[fsl| S (n : ℕ). e_len === (n : ℚ) ⬝ S (l : ℕ+). e_loc === (l : ℚ) ⬝
          ([⋆] i ∈ { ... n}. S (q:ℚ). (l+i : ℚ) ↦ q) ⋆ [[P]]
          ⊢ wrle [free(e_loc, e_len)] ([[P]] | [[RI]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    by_cases (∃ l : ℕ+, l = e_loc s.stack ∧ ∃ n : ℕ, n = e_len s.stack ∧ isAlloc s.heap l n)
    case pos h =>
      obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h
      rw [step_free s _ h_l h_n h_alloc, wrle_eq_of_term]
      rw [fslSup_apply]
      apply iSup_le
      intro n'
      simp only [fslMul, fslEquals, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
      split_ifs
      case neg => exact nonneg'
      case pos h_n' =>
        simp only [← h_n, Nat.cast_inj] at h_n'
        obtain rfl := h_n'
        apply iSup_le
        simp only [Subtype.forall, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        intro l'
        simp only [fslMul, fslEquals, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
        split_ifs
        case neg => exact nonneg'
        case pos h_l' =>
          apply sSup_le
          rintro _ ⟨heap₁, heap₂, h_disjoint, h_union, rfl⟩
          simp_rw [conservative_pointsTo, conservative_sup, conservative_bigSepMul]
          simp only [fslIverson, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
          split_ifs
          case pos h =>
            rw [SL.slBigSepCon_eq_one_iff_removedHeap] at h
            obtain ⟨h_removedHeap₁, h_alloc₁⟩ := h
            rw [removedHeap_of_union h_union.symm h_alloc₁] at h_removedHeap₁
            rw [h_removedHeap₁] at h_union h_disjoint
            rw [remainHeap_of_union_removeHeap h_union.symm h_disjoint]
            simp only [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
            rw [h_l']
            rfl
          case neg => simp only [zero_le]
    case neg h =>
      simp only [not_exists, not_and] at h
      rw [fslSup_apply]
      apply iSup_le
      intro n
      simp only [fslMul, fslEquals, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
      split_ifs
      case neg => exact nonneg'
      case pos h_n =>
        rw [fslSup_apply]
        apply iSup_le
        intro l
        simp only [fslMul, fslEquals, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
        split_ifs
        case neg => exact nonneg'
        case pos h_l =>
          specialize h l h_l.symm n h_n.symm
          apply sSup_le
          rintro _ ⟨heap₁, heap₂, _, h_union, rfl⟩
          simp_rw [conservative_pointsTo, conservative_sup, conservative_bigSepMul]
          simp only [fslIverson, iteOneZero_eq_ite, ite_mul, one_mul, zero_mul]
          split_ifs
          case neg => exact nonneg'
          case pos h_alloc =>
            rw [SL.slBigSepCon_eq_one_iff_removedHeap] at h_alloc
            exfalso
            apply h
            exact isAlloc_of_union_of_isAlloc h_alloc.right h_union.symm

end CFSL
