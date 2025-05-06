import LeanFSL.SL.Framing.Basic
import LeanFSL.SL.Fuzzy
import LeanFSL.CFSL.WeakExpectation
import LeanFSL.Mathlib.FixedPoints

namespace CFSL

open Syntax OrdinalApprox FSL State unitInterval

variable {Vars : Type}

private theorem gfpApprox_of_term_eq
    (h : v ∉ varRV P) (q : ℚ):
    gfpApprox (wrleStepHom P resource) ⊤ i [Prog| ↓] s
    = gfpApprox (wrleStepHom P resource) ⊤ i [Prog| ↓]
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  unfold gfpApprox
  rw [sInf_apply, iInf_apply, iInf_apply]
  apply congrArg
  apply funext
  simp only [Subtype.forall, exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
    forall_eq_or_imp, Pi.top_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply And.intro rfl
  intro i' _
  simp only [wrleStepHom, OrderHom.coe_mk, wrleStep]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h
  exact h s q

private theorem gfpApprox_of_term_fslSepMul_resource_eq
    (h : v ∉ varRV P ∪ varRV resource) (q : ℚ):
    `[fsl| [[gfpApprox (wrleStepHom P resource) ⊤ i [Prog| ↓] ]] ⋆ [[resource]]] s
    = `[fsl| [[gfpApprox (wrleStepHom P resource) ⊤ i [Prog| ↓] ]] ⋆ [[resource]]]
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [Set.mem_union, not_or] at h
  obtain ⟨h_P, h_resource⟩ := h
  simp only [fslSepMul]
  conv => {
    left; right; intro i; left; intro i; right; intro h₁
    rw [gfpApprox_of_term_eq h_P q]
  }
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_resource
  conv => {
    left; right; intro i; left; intro i; right; intro h₁; right; intro h₂
    rw [h_resource _ q]
  }

private theorem step_of_skip_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| skip] X s = step [Prog| skip] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  rw [step_skip, step_skip]
  apply h_ind
  simp only [varProg, Set.empty_union, Set.mem_union, not_or]
  simp only [Set.mem_union, not_or] at h
  exact h

private theorem step_of_assign_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| v' ≔ e] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| v' ≔ e] X s = step [Prog| v' ≔ e] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  rw [step_assign, step_assign]
  simp only [substituteStack]
  simp only [varProg, varValue, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_neq, h_expr⟩, h_P⟩, h_resource⟩ := h
  rw [h_ind]
  · rw [h_expr s.stack q]
    simp only
    rw [substituteVar_substituteVar_of_neq (Ne.symm h_neq)]
  · simp only [varProg, Set.empty_union, Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩

private theorem step_of_mutate_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| e *≔ e'] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| e *≔ e'] X s = step [Prog| e *≔ e'] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨h_e, h_e'⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    rw [step_mutate _ _ h_l h_alloc]
    rw [← h_e s.stack q] at h_l
    change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l ≠ HeapValue.undef at h_alloc
    rw [step_mutate _ _ h_l h_alloc]
    simp only [substituteHeap]
    rw [h_e' s.stack q]
    rw [h_ind]
    simp only [varProg, Set.empty_union, Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_neq_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_neq_alloc
    rw [step_mutate_of_abort _ _ h_neq_alloc]
    rw [← h_e s.stack q] at h_neq_alloc
    change ∀ l : ℕ+, e (substituteVar s.stack v q) = ↑↑l →
      (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l = HeapValue.undef at h_neq_alloc
    rw [step_mutate_of_abort _ _ h_neq_alloc]

private theorem step_of_lookup_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| v' ≔* e] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| v' ≔* e] X s = step [Prog| v' ≔* e] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValue, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_v', h_e⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    rw [neq_undef_iff_exists_val] at h_alloc
    obtain ⟨q', h_alloc⟩ := h_alloc
    rw [step_lookup _ _ h_l h_alloc]
    rw [← h_e s.stack q] at h_l
    change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l = q' at h_alloc
    rw [step_lookup _ _ h_l h_alloc]
    simp only [substituteStack]
    rw [substituteVar_substituteVar_of_neq h_v']
    rw [h_ind]
    simp only [varProg, Set.empty_union, Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_neq_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_neq_alloc
    rw [step_lookup_of_abort _ _ h_neq_alloc]
    rw [← h_e s.stack q] at h_neq_alloc
    change ∀ (x : ℕ+), e (substituteVar s.stack v q) = ↑↑x →
      (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap x = HeapValue.undef at h_neq_alloc
    rw [step_lookup_of_abort _ _ h_neq_alloc]

private theorem step_of_compareAndSet_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| v' ≔ cas(e_l, e_c, e_s)] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| v' ≔ cas(e_l, e_c, e_s)] X s
    = step [Prog| v' ≔ cas(e_l, e_c, e_s)] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValue, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨⟨⟨h_v', h_el⟩, h_ec⟩, h_es⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e_l s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    cases eq_or_ne (s.heap l) (e_c s.stack) with
    | inl h_eq =>
      rw [step_cas_of_eq _ _ h_l h_eq]
      rw [← h_el _ q] at h_l
      rw [← h_ec _ q] at h_eq
      change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l
        = HeapValue.val (e_c (substituteVar s.stack v q)) at h_eq
      rw [step_cas_of_eq _ _ h_l h_eq]
      simp only [substituteStack, substituteHeap]
      rw [h_es _ q]
      rw [substituteVar_substituteVar_of_neq h_v']
      rw [h_ind]
      simp only [varProg, Set.empty_union, Set.mem_union, not_or]
      exact ⟨h_P, h_resource⟩
    | inr h_neq =>
      rw [step_cas_of_neq _ _ h_l h_alloc h_neq]
      rw [← h_el _ q] at h_l
      change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l ≠ HeapValue.undef at h_alloc
      change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l ≠ (e_c s.stack) at h_neq
      rw [← h_ec _ q] at h_neq
      rw [step_cas_of_neq _ _ h_l h_alloc h_neq]
      simp only [substituteStack]
      rw [substituteVar_substituteVar_of_neq h_v']
      rw [h_ind]
      simp only [varProg, Set.empty_union, Set.mem_union, not_or]
      exact ⟨h_P, h_resource⟩
  case neg h_ne_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_ne_alloc
    rw [step_cas_of_abort _ _ h_ne_alloc]
    change ∀ (x : ℕ+), e_l s.stack = ↑↑x
      → (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap x = HeapValue.undef at h_ne_alloc
    rw [← h_el _ q] at h_ne_alloc
    rw [step_cas_of_abort _ _ h_ne_alloc]

private theorem step_of_allocate_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| v' ≔ alloc(e)] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| v' ≔ alloc(e)] X s
    = step [Prog| v' ≔ alloc(e)] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValue, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_v', h_e⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ n : ℕ, e s.stack = n
  case pos h_n =>
    obtain ⟨n, h_n⟩ := h_n
    rw [step_alloc _ _ h_n]
    rw [← h_e _ q] at h_n
    rw [step_alloc _ _ h_n]
    simp only [substituteStack, allocateHeap]
    conv => {
      right; right; intro i; left; intro i; right; intro l; right
      rw [substituteVar_substituteVar_of_neq h_v']
    }
    have : v ∉ varProg [Prog| ↓] ∪ varRV P ∪ varRV resource := by {
      simp only [varProg, Set.empty_union, Set.mem_union, not_or]
      exact ⟨h_P, h_resource⟩
    }
    conv => {
      left; right; intro i; left; intro i; right; intro l; right
      rw [h_ind this]
    }
  case neg h_n =>
    simp only [not_exists] at h_n
    rw [step_alloc_of_abort _ _ h_n]
    rw [← h_e _ q] at h_n
    rw [step_alloc_of_abort _ _ h_n]

private theorem step_of_free_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| free(e_l, e_n)] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| free(e_l, e_n)] X s
    = step [Prog| free(e_l, e_n)] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValue, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨h_el, h_en⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, l = e_l s.stack ∧ ∃ n : ℕ, n = e_n s.stack ∧ isAlloc s.heap l n
  case pos h_alloc =>
    obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h_alloc
    rw [step_free _ _ h_l h_n h_alloc]
    rw [← h_el _ q] at h_l
    rw [← h_en _ q] at h_n
    change isAlloc (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l n at h_alloc
    rw [step_free _ _ h_l h_n h_alloc]
    simp only [freeHeap]
    rw [h_ind]
    simp only [varProg, Set.empty_union, Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_abort =>
    simp only [not_exists, not_and] at h_abort
    rw [step_free_of_abort _ _ h_abort]
    rw [← h_el _ q, ← h_en _ q] at h_abort
    conv at h_abort => {
      intro l h n h; right
      change isAlloc (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l n
    }
    rw [step_free_of_abort _ _ h_abort]

private theorem step_of_probBranching_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| pif e then [[c₁]] else [[c₂]] fi] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| pif e then [[c₁]] else [[c₂]] fi] X s
    = step [Prog| pif e then [[c₁]] else [[c₂]] fi] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varProb, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨⟨h_e, h_c₁⟩, h_c₂⟩, h_P⟩, h_resource⟩ := h
  rw [step_probChoice, step_probChoice]
  rw [← h_e _ q]
  simp only
  rw [h_ind]
  · nth_rw 2 [h_ind]
    simp only [Set.mem_union, not_or]
    exact ⟨⟨h_c₂, h_P⟩, h_resource⟩
  · simp only [Set.mem_union, not_or]
    exact ⟨⟨h_c₁, h_P⟩, h_resource⟩

private theorem step_of_condBranching_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| if e then [[c₁]] else [[c₂]] fi] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| if e then [[c₁]] else [[c₂]] fi] X s
    = step [Prog| if e then [[c₁]] else [[c₂]] fi] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varBool, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨⟨h_e, h_c₁⟩, h_c₂⟩, h_P⟩, h_resource⟩ := h
  by_cases (e s.stack)
  case pos h =>
    rw [step_condChoice_left _ _ h]
    rw [← h_e _ q] at h
    rw [step_condChoice_left _ _ h]
    rw [h_ind]
    simp only [Set.mem_union, not_or]
    exact ⟨⟨h_c₁, h_P⟩, h_resource⟩
  case neg h =>
    simp only [Bool.not_eq_true] at h
    rw [step_condChoice_right _ _ h]
    rw [← h_e _ q] at h
    rw [step_condChoice_right _ _ h]
    rw [h_ind]
    simp only [Set.mem_union, not_or]
    exact ⟨⟨h_c₂, h_P⟩, h_resource⟩

private theorem step_of_loop_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| while e begin [[c]] fi] ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step [Prog| while e begin [[c]] fi] X s
    = step [Prog| while e begin [[c]] fi] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varBool, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨h_e, h_c⟩, h_P⟩, h_resource⟩ := h
  by_cases (e s.stack)
  case pos h =>
    rw [step_loop_cont _ _ h]
    rw [← h_e _ q] at h
    rw [step_loop_cont _ _ h]
    rw [h_ind]
    simp only [varProg, varBool, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
      Decidable.not_not]
    exact ⟨⟨⟨h_c, h_e, h_c⟩, h_P⟩, h_resource⟩
  case neg h =>
    simp only [Bool.not_eq_true] at h
    rw [step_loop_term _ _ h]
    rw [← h_e _ q] at h
    rw [step_loop_term _ _ h]
    rw [h_ind]
    simp only [varProg, Set.empty_union, Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩

private theorem step_of_sequential_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| [[c₁]] ; [[c₂]]] ∪ varRV P ∪ varRV resource)
    (h_ind_X : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩)
    (h_ind₁ : ∀ {X : Program Vars → StateRV Vars}, v ∉ varProg c₁ ∪ varRV P ∪ varRV resource →
      (∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource →
          X c' s' = X c' { stack := substituteVar s'.stack v q, heap := s'.heap }) →
      step c₁ X s = step c₁ X { stack := substituteVar s.stack v q, heap := s.heap }) :
    step [Prog| [[c₁]] ; [[c₂]]] X s
    = step [Prog| [[c₁]] ; [[c₂]]] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, Set.mem_union, not_or] at h
  obtain ⟨⟨⟨h_c₁, h_c₂⟩, h_P⟩, h_resource⟩ := h
  cases eq_or_ne c₁ [Prog| ↯] with
  | inl h_c₁_abort =>
    rw [h_c₁_abort, step_sequential_abort, step_sequential_abort]
  | inr h_c₁_neq_abort =>
    cases eq_or_ne c₁ [Prog| ↓] with
    | inl h_c₁_term =>
      rw [h_c₁_term, step_sequential_term, step_sequential_term]
      rw [h_ind_X]
      simp only [Set.mem_union, not_or]
      exact ⟨⟨h_c₂, h_P⟩, h_resource⟩
    | inr h_c₁_neq_term =>
      rw [step_sequential_cont _ _ h_c₁_neq_term h_c₁_neq_abort]
      rw [step_sequential_cont _ _ h_c₁_neq_term h_c₁_neq_abort]
      rw [h_ind₁]
      · simp only [Set.mem_union, not_or]
        exact ⟨⟨h_c₁, h_P⟩, h_resource⟩
      · intro c' s' h
        simp only [Set.mem_union, not_or] at h
        obtain ⟨⟨h_c', _⟩, _⟩ := h
        rw [h_ind_X]
        simp only [varProg, Set.mem_union, not_or]
        exact ⟨⟨⟨h_c', h_c₂⟩, h_P⟩, h_resource⟩

private theorem step_of_concurrent_eq_of_not_mem_vars {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| [[c₁]] || [[c₂]]] ∪ varRV P ∪ varRV resource)
    (h_ind_X : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩)
    (h_ind₁ : ∀ {X : Program Vars → StateRV Vars}, v ∉ varProg c₁ ∪ varRV P ∪ varRV resource →
      (∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource →
          X c' s' = X c' { stack := substituteVar s'.stack v q, heap := s'.heap }) →
      step c₁ X s = step c₁ X { stack := substituteVar s.stack v q, heap := s.heap })
    (h_ind₂ : ∀ {X : Program Vars → StateRV Vars}, v ∉ varProg c₂ ∪ varRV P ∪ varRV resource →
      (∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource →
          X c' s' = X c' { stack := substituteVar s'.stack v q, heap := s'.heap }) →
      step c₂ X s = step c₂ X { stack := substituteVar s.stack v q, heap := s.heap }) :
    step [Prog| [[c₁]] || [[c₂]]] X s
    = step [Prog| [[c₁]] || [[c₂]]] X ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, Set.mem_union, not_or] at h
  obtain ⟨⟨⟨h_c₁, h_c₂⟩, h_P⟩, h_resource⟩ := h
  cases eq_or_ne c₁ [Prog| ↯] with
  | inl h_c₁_abort =>
    rw [h_c₁_abort, step_concurrent_abort_left, step_concurrent_abort_left]
  | inr h_c₁_neq_abort =>
    cases eq_or_ne c₂ [Prog| ↯] with
    | inl h_c₂_abort =>
      rw [h_c₂_abort, step_concurrent_abort_right, step_concurrent_abort_right]
    | inr h_c₂_neq_abort =>
      cases eq_or_ne c₁ [Prog| ↓] with
      | inl h_c₁_term =>
        rw [h_c₁_term]
        cases eq_or_ne c₂ [Prog| ↓] with
        | inl h_c₂_term =>
          rw [h_c₂_term, step_concurrent_term, step_concurrent_term]
          rw [h_ind_X]
          simp only [varProg, Set.empty_union, Set.mem_union, not_or]
          exact ⟨h_P, h_resource⟩
        | inr h_c₂_neq_term =>
          rw [step_concurrent_cont_only_right _ _ h_c₂_neq_term h_c₂_neq_abort]
          rw [step_concurrent_cont_only_right _ _ h_c₂_neq_term h_c₂_neq_abort]
          rw [h_ind₂]
          · simp only [Set.mem_union, not_or]
            exact ⟨⟨h_c₂, h_P⟩, h_resource⟩
          · intro c' s' h
            simp only [Set.mem_union, not_or] at h
            obtain ⟨⟨h_c', _⟩, _⟩ := h
            rw [h_ind_X]
            simp only [varProg, Set.empty_union, Set.mem_union, not_or]
            exact ⟨⟨h_c', h_P⟩, h_resource⟩
      | inr h_c₁_neq_term =>
        cases eq_or_ne c₂ [Prog| ↓] with
        | inl h_c₂_term =>
          rw [h_c₂_term]
          rw [step_concurrent_cont_only_left _ _ h_c₁_neq_term h_c₁_neq_abort]
          rw [step_concurrent_cont_only_left _ _ h_c₁_neq_term h_c₁_neq_abort]
          rw [h_ind₁]
          · simp only [Set.mem_union, not_or]
            exact ⟨⟨h_c₁, h_P⟩, h_resource⟩
          · intro c' s' h
            simp only [Set.mem_union, not_or] at h
            obtain ⟨⟨h_c', _⟩, _⟩ := h
            rw [h_ind_X]
            simp only [varProg, Set.union_empty, Set.mem_union, not_or]
            exact ⟨⟨h_c', h_P⟩, h_resource⟩
        | inr h_c₂_neq_term =>
          rw [step_concurrent_cont _ _ h_c₁_neq_term h_c₂_neq_term h_c₁_neq_abort h_c₂_neq_abort]
          rw [step_concurrent_cont _ _ h_c₁_neq_term h_c₂_neq_term h_c₁_neq_abort h_c₂_neq_abort]
          rw [h_ind₁]
          · rw [h_ind₂]
            · simp only [Set.mem_union, not_or]
              exact ⟨⟨h_c₂, h_P⟩, h_resource⟩
            · intro c' s' h
              simp only [Set.mem_union, not_or] at h
              obtain ⟨⟨h_c', _⟩, _⟩ := h
              rw [h_ind_X]
              simp only [varProg, Set.mem_union, not_or]
              exact ⟨⟨⟨h_c₁, h_c'⟩, h_P⟩, h_resource⟩
          · simp only [Set.mem_union, not_or]
            exact ⟨⟨h_c₁, h_P⟩, h_resource⟩
          · intro c' s' h
            simp only [Set.mem_union, not_or] at h
            obtain ⟨⟨h_c', _⟩, _⟩ := h
            rw [h_ind_X]
            simp only [varProg, Set.mem_union, not_or]
            exact ⟨⟨⟨h_c', h_c₂⟩, h_P⟩, h_resource⟩

private theorem step_eq_of_not_mem_vars {c : Program Vars} {P resource : StateRV Vars}
    {X : Program Vars → StateRV Vars} (s : State Vars)
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c' : Program Vars} {s' : State Vars}, v ∉ varProg c' ∪ varRV P ∪ varRV resource
      → X c' s' = X c' ⟨substituteVar s'.stack v q, s'.heap⟩) :
    step c X s = step c X ⟨substituteVar s.stack v q, s.heap⟩ := by
  induction c generalizing X with
  | terminated => simp [step]
  | abort => simp [step]
  | skip' =>
    simp only [varProg, Set.empty_union] at h
    exact step_of_skip_eq_of_not_mem_vars s h h_ind
  | assign v' e => exact step_of_assign_eq_of_not_mem_vars s h h_ind
  | mutate e e' => exact step_of_mutate_eq_of_not_mem_vars s h h_ind
  | lookup v' e => exact step_of_lookup_eq_of_not_mem_vars s h h_ind
  | compareAndSet v' e_l e_c _s => exact step_of_compareAndSet_eq_of_not_mem_vars s h h_ind
  | allocate v' e => exact step_of_allocate_eq_of_not_mem_vars s h h_ind
  | free' e_l e_n => exact step_of_free_eq_of_not_mem_vars s h h_ind
  | probabilisticBranching e c₁ c₂ => exact step_of_probBranching_eq_of_not_mem_vars s h h_ind
  | conditionalBranching e c₁ c₂ => exact step_of_condBranching_eq_of_not_mem_vars s h h_ind
  | loop e c => exact step_of_loop_eq_of_not_mem_vars s h h_ind
  | sequential c₁ c₂ ih₁ => exact step_of_sequential_eq_of_not_mem_vars s h h_ind ih₁
  | concurrent c₁ c₂ ih₁ ih₂ => exact step_of_concurrent_eq_of_not_mem_vars s h h_ind ih₁ ih₂

private theorem gfpApprox_eq_of_not_mem_vars {c : Program Vars} {P resource : StateRV Vars}
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource) :
    gfpApprox (wrleStepHom P resource) ⊤ i c s
    = gfpApprox (wrleStepHom P resource) ⊤ i c ⟨substituteVar s.stack v q, s.heap⟩ := by
  induction i using Ordinal.induction generalizing c s with
  | h i ih =>
    have h_vars := h
    simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
      Decidable.not_not] at h
    obtain ⟨⟨_, h_P⟩, h_resource⟩ := h
    unfold gfpApprox
    rw [sInf_apply, iInf_apply, iInf_apply]
    apply congrArg
    apply funext
    simp only [Subtype.forall, exists_prop, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_setOf_eq, forall_eq_or_imp, Pi.top_apply, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · rfl
    · intro i' h_i'
      rw [wrleStepHom, OrderHom.coe_mk]
      cases eq_or_ne c [Prog| ↓] with
      | inl h_term =>
        rw [h_term, wrleStep, h_P _ q]
      | inr h_neq_term =>
        cases eq_or_ne c [Prog| ↯] with
        | inl h_abort =>
          rw [h_abort]
          rfl
        | inr h_neq_abort =>
          rw [wrleStep]
          · simp only [fslSepDiv]
            conv => {
              left; right; intro i; left; intro i; right; intro h'
              rw [h_resource _ q]
            }
            conv => {
              left; right; intro i; left; intro i; right; intro h'
              right; right; left; left; intro c
              change `[fsl| [[gfpApprox (wrleStepHom P resource) ⊤ i' c]] ⋆ [[resource]] ]
            }
            have : ∀ k < i, ∀ {c : Program Vars} {s : State Vars},
              v ∉ varProg c ∪ varRV P ∪ varRV resource →
              (`[fsl| [[gfpApprox (wrleStepHom P resource) ⊤ k c]] ⋆ [[resource]] ]) s =
              (`[fsl| [[gfpApprox (wrleStepHom P resource) ⊤ k c]] ⋆ [[resource]] ])
                ⟨substituteVar s.stack v q, s.heap⟩ := by {
              intro i' h_i' c s h_vars
              simp only [fslSepMul]
              conv => {
                left; right; intro a; left; intro a; right; intro h₁
                rw [ih i' h_i' h_vars]
              }
              simp only
              simp only [varRV, substituteStack, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or,
                not_exists, Decidable.not_not] at h_vars
              obtain ⟨_, h_resource⟩ := h_vars
              conv => {
                left; right; intro a; left; intro a; right; intro h₁; right; intro h₂
                rw [h_resource _ q]
              }
            }
            conv => {
              left; right; intro i; left; intro i; right; intro h'
              rw [step_eq_of_not_mem_vars _ h_vars (this i' h_i')]
            }
            rfl
          · exact h_neq_term
          · exact h_neq_abort

theorem varRV_of_gfpApprox_wrleStep {P resource : StateRV Var} :
    varRV (gfpApprox (wrleStepHom P resource) ⊤ i c)
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  exact gfpApprox_eq_of_not_mem_vars h_v

theorem varRV_of_wrle :
    varRV `[fsl Var| wrle [c] ([[P]]|[[resource]])]
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, State.substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  unfold wrle'
  rw [← gfpApprox_ord_eq_gfp]
  exact gfpApprox_eq_of_not_mem_vars h_v


end CFSL
