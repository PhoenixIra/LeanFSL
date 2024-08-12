import InvLimDiss.SL.Framing.Basic
import InvLimDiss.SL.Quantitative
import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.Mathlib.FixedPoints

namespace CQSL

open Syntax OrdinalApprox QSL State unitInterval

variable {Vars : Type}

private theorem gfpApprox_of_term_eq
    (h : v ∉ varRV P) (q : ℚ):
    gfpApprox (wrle_step_hom P resource) ⊤ i [Prog| ↓] s
    = gfpApprox (wrle_step_hom P resource) ⊤ i [Prog| ↓]
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  unfold gfpApprox
  rw [sInf_apply, iInf_apply, iInf_apply]
  apply congrArg
  apply funext
  simp only [Subtype.forall, exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq,
    forall_eq_or_imp, Pi.top_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply And.intro rfl
  intro i' _
  simp only [wrle_step_hom, OrderHom.coe_mk, wrle_step]
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h
  exact h s q

private theorem gfpApprox_of_term_qslSepMul_resource_eq
    (h : v ∉ varRV P ∪ varRV resource) (q : ℚ):
    `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i [Prog| ↓] ]] ⋆ [[resource]]] s
    = `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i [Prog| ↓] ]] ⋆ [[resource]]]
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [Set.mem_union, not_or] at h
  obtain ⟨h_P, h_resource⟩ := h
  simp only [qslSepMul]
  conv => {
    left; right; intro i; left; intro i; right; intro h₁
    rw [gfpApprox_of_term_eq h_P q]
  }
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not] at h_resource
  conv => {
    left; right; intro i; left; intro i; right; intro h₁; right; intro h₂
    rw [h_resource _ q]
  }

private theorem step_of_term_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varRV P ∪ varRV resource) :
    step [Prog| skip]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| skip]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  rw [step_skip, step_skip]
  rw [gfpApprox_of_term_qslSepMul_resource_eq h q]

private theorem step_of_assign_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v' ∉ varProg [Prog| v ≔ e] ∪ varRV P ∪ varRV resource) :
    step [Prog| v ≔ e]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| v ≔ e]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v' q, s.heap⟩ := by
  rw [step_assign, step_assign]
  simp only [substituteStack]
  simp only [varProg, varValueExp, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_neq, h_expr⟩, h_P⟩, h_resource⟩ := h
  rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
  · rw [h_expr s.stack q]
    simp only
    rw [substituteVar_substituteVar_of_neq h_neq]
  · simp only [Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩

private theorem step_of_mutate_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| e *≔ e'] ∪ varRV P ∪ varRV resource) :
    step [Prog|e *≔ e']
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| e *≔ e']
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValueExp, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨h_e, h_e'⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    rw [step_mutate _ _ h_l h_alloc]
    rw [h_e s.stack q] at h_l
    change (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l ≠ HeapValue.undef at h_alloc
    rw [step_mutate _ _ h_l h_alloc]
    simp only [substituteHeap]
    rw [h_e' s.stack q]
    rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
    simp only [Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_neq_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_neq_alloc
    rw [step_mutate_of_abort _ _ h_neq_alloc]
    rw [h_e s.stack q] at h_neq_alloc
    change ∀ l : ℕ+, e (substituteVar s.stack v q) = ↑↑l →
      (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l = HeapValue.undef at h_neq_alloc
    rw [step_mutate_of_abort _ _ h_neq_alloc]

private theorem step_of_lookup_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v' ∉ varProg [Prog| v ≔* e] ∪ varRV P ∪ varRV resource) :
    step [Prog| v ≔* e]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| v ≔* e]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v' q, s.heap⟩ := by
  simp only [varProg, varValueExp, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_v', h_e⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    rw [neq_undef_iff_exists_val] at h_alloc
    obtain ⟨q', h_alloc⟩ := h_alloc
    rw [step_lookup _ _ h_l h_alloc]
    rw [h_e s.stack q] at h_l
    change (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap l = q' at h_alloc
    rw [step_lookup _ _ h_l h_alloc]
    simp only [substituteStack]
    rw [substituteVar_substituteVar_of_neq h_v']
    rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
    simp only [Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_neq_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_neq_alloc
    rw [step_lookup_of_abort _ _ h_neq_alloc]
    rw [h_e s.stack q] at h_neq_alloc
    change ∀ (x : ℕ+), e (substituteVar s.stack v' q) = ↑↑x →
      (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap x = HeapValue.undef at h_neq_alloc
    rw [step_lookup_of_abort _ _ h_neq_alloc]

private theorem step_of_compareAndSet_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v' ∉ varProg [Prog| v ≔ cas(e_l, e_c, e_s)] ∪ varRV P ∪ varRV resource) :
    step [Prog| v ≔ cas(e_l, e_c, e_s)]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| v ≔ cas(e_l, e_c, e_s)]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v' q, s.heap⟩ := by
  simp only [varProg, varValueExp, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨⟨⟨h_v', h_el⟩, h_ec⟩, h_es⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, e_l s.stack = l ∧ s.heap l ≠ HeapValue.undef
  case pos h_alloc =>
    obtain ⟨l, h_l, h_alloc⟩ := h_alloc
    cases eq_or_ne (s.heap l) (e_c s.stack) with
    | inl h_eq =>
      rw [step_cas_of_eq _ _ h_l h_eq]
      rw [h_el _ q] at h_l
      rw [h_ec _ q] at h_eq
      change (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap l
        = HeapValue.val (e_c (substituteVar s.stack v' q)) at h_eq
      rw [step_cas_of_eq _ _ h_l h_eq]
      simp only [substituteStack, substituteHeap]
      rw [h_es _ q]
      rw [substituteVar_substituteVar_of_neq h_v']
      rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
      simp only [Set.mem_union, not_or]
      exact ⟨h_P, h_resource⟩
    | inr h_neq =>
      rw [step_cas_of_neq _ _ h_l h_alloc h_neq]
      rw [h_el _ q] at h_l
      change (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap l ≠ HeapValue.undef at h_alloc
      change (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap l ≠ (e_c s.stack) at h_neq
      rw [h_ec _ q] at h_neq
      rw [step_cas_of_neq _ _ h_l h_alloc h_neq]
      simp only [substituteStack]
      rw [substituteVar_substituteVar_of_neq h_v']
      rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
      simp only [Set.mem_union, not_or]
      exact ⟨h_P, h_resource⟩
  case neg h_ne_alloc =>
    simp only [ne_eq, not_exists, not_and, not_not] at h_ne_alloc
    rw [step_cas_of_abort _ _ h_ne_alloc]
    change ∀ (x : ℕ+), e_l s.stack = ↑↑x
      → (⟨substituteVar s.stack v' q, s.heap⟩ : State Vars).heap x = HeapValue.undef at h_ne_alloc
    rw [h_el _ q] at h_ne_alloc
    rw [step_cas_of_abort _ _ h_ne_alloc]

private theorem step_of_allocate_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v' ∉ varProg [Prog| v ≔ alloc(e)] ∪ varRV P ∪ varRV resource) :
    step [Prog| v ≔ alloc(e)]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| v ≔ alloc(e)]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v' q, s.heap⟩ := by
  simp only [varProg, varValueExp, ne_eq, Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
    Set.mem_setOf_eq, not_or, not_exists, Decidable.not_not] at h
  obtain ⟨⟨⟨h_v', h_e⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ n : ℕ, e s.stack = n
  case pos h_n =>
    obtain ⟨n, h_n⟩ := h_n
    rw [step_alloc _ _ h_n]
    rw [h_e _ q] at h_n
    rw [step_alloc _ _ h_n]
    simp only [substituteStack, allocateHeap]
    conv => {
      right; right; intro i; left; intro i; right; intro l; right
      rw [substituteVar_substituteVar_of_neq h_v']
    }
    have : v' ∉ varRV P ∪ varRV resource := by {simp only [Set.mem_union, not_or]; exact ⟨h_P, h_resource⟩}
    conv => {
      left; right; intro i; left; intro i; right; intro l; right
      rw [gfpApprox_of_term_qslSepMul_resource_eq this q]
    }
  case neg h_n =>
    simp only [not_exists] at h_n
    rw [step_alloc_of_abort _ _ h_n]
    rw [h_e _ q] at h_n
    rw [step_alloc_of_abort _ _ h_n]

private theorem step_of_free_eq_of_not_mem_vars  {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg [Prog| free(e_l, e_n)] ∪ varRV P ∪ varRV resource) :
    step [Prog| free(e_l, e_n)]
        (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step [Prog| free(e_l, e_n)]
       (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  simp only [varProg, varValueExp, ne_eq, Set.mem_union, Set.mem_setOf_eq, not_or, not_exists,
    Decidable.not_not] at h
  obtain ⟨⟨⟨h_el, h_en⟩, h_P⟩, h_resource⟩ := h
  by_cases ∃ l : ℕ+, l = e_l s.stack ∧ ∃ n : ℕ, n = e_n s.stack ∧ isAlloc s.heap l n
  case pos h_alloc =>
    obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h_alloc
    rw [step_free _ _ h_l h_n h_alloc]
    rw [h_el _ q] at h_l
    rw [h_en _ q] at h_n
    change isAlloc (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l n at h_alloc
    rw [step_free _ _ h_l h_n h_alloc]
    simp only [freeHeap]
    rw [gfpApprox_of_term_qslSepMul_resource_eq ?_ q]
    simp only [Set.mem_union, not_or]
    exact ⟨h_P, h_resource⟩
  case neg h_abort =>
    simp only [not_exists, not_and] at h_abort
    rw [step_free_of_abort _ _ h_abort]
    rw [h_el _ q, h_en _ q] at h_abort
    conv at h_abort => {
      intro l h n h; right
      change isAlloc (⟨substituteVar s.stack v q, s.heap⟩ : State Vars).heap l n
    }
    rw [step_free_of_abort _ _ h_abort]



private theorem step_eq_of_not_mem_vars {c : Program Vars} {P resource : StateRV Vars} (s : State Vars)
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource)
    (h_ind : ∀ {c : Program Vars} {s : State Vars}, v ∉ varProg c ∪ varRV P ∪ varRV resource →
      gfpApprox (wrle_step_hom P resource) ⊤ i' c s
      = gfpApprox (wrle_step_hom P resource) ⊤ i' c ⟨substituteVar s.stack v q, s.heap⟩) :
    step c (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]) s
    = step c (fun c ↦ `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ])
      ⟨substituteVar s.stack v q, s.heap⟩ := by
  induction c with
  | terminated => simp [step]
  | abort => simp [step]
  | skip' =>
    simp only [varProg, Set.empty_union] at h
    exact step_of_term_eq_of_not_mem_vars s h
  | assign v' e => exact step_of_assign_eq_of_not_mem_vars s h
  | mutate e e' => exact step_of_mutate_eq_of_not_mem_vars s h
  | lookup v' e => exact step_of_lookup_eq_of_not_mem_vars s h
  | compareAndSet v' e_l e_c _s => exact step_of_compareAndSet_eq_of_not_mem_vars s h
  | allocate v' e => exact step_of_allocate_eq_of_not_mem_vars s h
  | free' e_l e_n => exact step_of_free_eq_of_not_mem_vars s h
  | probabilisticBranching e c₁ c₂ => sorry
  | conditionalBranching e c₁ c₂ => sorry
  | loop e c => sorry
  | sequential c₁ c₂ ih₁ => sorry
  | concurrent c₁ c₂ ih₁ ih₂ => sorry

private theorem gfpApprox_eq_of_not_mem_vars
    (h : v ∉ varProg c ∪ varRV P ∪ varRV resource) :
    gfpApprox (wrle_step_hom P resource) ⊤ i c s
    = gfpApprox (wrle_step_hom P resource) ⊤ i c ⟨substituteVar s.stack v q, s.heap⟩ := by
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
      rw [wrle_step_hom, OrderHom.coe_mk, wrle_step]
      cases eq_or_ne c [Prog| ↓] with
      | inl h_term =>
        rw [h_term]
        simp only
        rw [h_P _ q]
      | inr h_neq_term =>
        cases eq_or_ne c [Prog| ↯] with
        | inl h_abort =>
          rw [h_abort]
          rfl
        | inr h_neq_abort =>
          simp only [qslSepDiv]
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            rw [h_resource _ q]
          }
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            right; right; left; left; intro c
            change `[qsl| [[gfpApprox (wrle_step_hom P resource) ⊤ i' c]] ⋆ [[resource]] ]
          }
          conv => {
            left; right; intro i; left; intro i; right; intro h'
            rw [step_eq_of_not_mem_vars _ h_vars (ih i' h_i')]
          }
          rfl

theorem varRV_of_gfpApprox_wrle_step {P resource : StateRV Var} :
    varRV (gfpApprox (wrle_step_hom P resource) ⊤ i c)
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  exact gfpApprox_eq_of_not_mem_vars h_v

theorem varRV_of_wrle :
    varRV `[qsl Var| wrle [c] ([[P]]|[[resource]])]
    ⊆ varProg c ∪ varRV P ∪ varRV resource := by
  intro v h_v
  contrapose h_v
  simp only [varRV, State.substituteStack, ne_eq, Set.mem_setOf_eq, not_exists, Decidable.not_not]
  intro s q
  unfold wrle'
  rw [← gfpApprox_ord_eq_gfp]
  exact gfpApprox_eq_of_not_mem_vars h_v


end CQSL
