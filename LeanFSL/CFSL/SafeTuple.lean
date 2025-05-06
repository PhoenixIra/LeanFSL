import LeanFSL.CFSL.Proofrules
import LeanFSL.SL.Framing.VarApprox

namespace CFSL

open FSL Syntax Atom

def safeTuple (RI P Q : StateRV Var) (c : Program Var) : Prop :=
    `[fsl| [[P]] ⊢ wrle [c] ([[Q]] | [[RI]])]

syntax " ⊢ " fsl " ⦃ " fsl " ⦄ " term " ⦃ " fsl " ⦄ " : term
macro_rules
  | `(term| ⊢ $ri:fsl ⦃ $p:fsl ⦄ $c:term ⦃ $q:fsl ⦄ ) =>
    `(safeTuple `[fsl| $ri] `[fsl| $p] `[fsl| $q] $c)

syntax " ⊢ " fsl " ⦃ " fsl " ⦄ " program " ⦃ " fsl " ⦄ " : term
macro_rules
  | `(term| ⊢ $ri:fsl ⦃ $p:fsl ⦄ $c:program ⦃ $q:fsl ⦄ ) =>
    `(safeTuple `[fsl| $ri] `[fsl| $p] `[fsl| $q] [Prog| $c])

open Lean PrettyPrinter Delaborator

@[app_unexpander safeTuple]
def unexpandeSafeTuple : Unexpander
  | `($_ $ri $p $q [Prog| $c:program]) =>
      do `( ⊢ $(← makeBrackets ri):fsl ⦃$(← makeBrackets p):fsl⦄ $c:program ⦃$(← makeBrackets q):fsl⦄)
  | `($_ $ri $p $q $c:term) =>
      do `( ⊢ $(← makeBrackets ri):fsl ⦃$(← makeBrackets p):fsl⦄ $c:term ⦃$(← makeBrackets q):fsl⦄)
  | _ => throw ()

theorem safeTuple_skip (RI P : StateRV Var) : ⊢ [[RI]] ⦃[[P]]⦄ skip ⦃[[P]]⦄ := wrle_skip

theorem safeTuple_assign (P : StateRV Var) (h : v ∉ varRV RI) : ⊢ [[RI]] ⦃[[P]](v ↦ e)⦄ v ≔ e ⦃[[P]]⦄ :=
    wrle_assign h

theorem safeTuple_mutate (P : StateRV Var) :
    ⊢ [[RI]] ⦃(S (q : ℚ). e_loc ↦ q) ⋆ (e_loc ↦ e_val -⋆ [[P]])⦄ e_loc *≔ e_val ⦃[[P]]⦄ :=
  wrle_mutate

theorem safeTuple_lookup (P : StateRV Var) (h : v ∉ varRV RI) :
    ⊢ [[RI]] ⦃S (q : ℚ). e_loc ↦ q ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ q))⦄ v ≔* e_loc ⦃[[P]]⦄ :=
  wrle_lookup h

theorem safeTuple_cas_true (P : StateRV Var) (h : v ∉ varRV RI) :
    ⊢ [[RI]] ⦃e_loc ↦ e_val ⋆ (e_loc ↦ e_set -⋆ [[P]](v ↦ (1:ℚ)))⦄ v ≔ cas(e_loc, e_val, e_set) ⦃[[P]]⦄ :=
  wrle_compareAndSet_true h

theorem safeTuple_cas_false (P : StateRV Var) (h : v ∉ varRV RI) :
    ⊢ [[RI]] ⦃S (q : ℚ). (e_loc ↦ q ⬝ ~(q === e_val)) ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ (0:ℚ)))⦄
    v ≔ cas(e_loc, e_val, e_set) ⦃[[P]]⦄ :=
  wrle_compareAndSet_false h

theorem safeTuple_cas (P : StateRV Var) (h : v ∉ varRV RI) :
    ⊢ [[RI]] ⦃
      e_loc ↦ e_val ⋆ (e_loc ↦ e_set -⋆ [[P]](v ↦ (1:ℚ)))
      ⊔ S (q : ℚ). (e_loc ↦ q ⬝ ~(q === e_val)) ⋆ (e_loc ↦ q -⋆ [[P]](v ↦ (0:ℚ)))⦄
    v ≔ cas(e_loc, e_val, e_set) ⦃[[P]]⦄ :=
  wrle_compareAndSet h

theorem safeTuple_allocate (P : StateRV Var) (h : v ∉ varRV RI) :
    ⊢ [[RI]] ⦃S (n : ℕ). e_len === (n : ℚ) ⬝ I (l : ℕ+).
          ([⋆] i ∈ { ... n}. (l+i : ℚ) ↦ (0:ℚ)) -⋆ [[P]](v ↦ (l:ℚ))⦄
    v ≔ alloc(e_len) ⦃[[P]]⦄ :=
  wrle_allocate h

theorem safeTuple_free (P : StateRV Var) :
    ⊢ [[RI]] ⦃S (n : ℕ). e_len === (n : ℚ) ⬝ S (l : ℕ+). e_loc === (l : ℚ) ⬝
          ([⋆] i ∈ { ... n}. S (q:ℚ). (l+i : ℚ) ↦ q) ⋆ [[P]]⦄
    free(e_loc, e_len) ⦃[[P]]⦄ :=
  wrle_free

theorem safeTuple_probabilisticBranching
    ( h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c₁ ⦃[[P]]⦄)
    ( h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c₂ ⦃[[P]]⦄) :
    ⊢ [[RI]] ⦃<e> ⬝ [[Q₁]] + ~<e> ⬝ [[Q₂]]⦄
    pif e then [[c₁]] else [[c₂]] fi ⦃[[P]]⦄ := by
  apply le_trans ?_ wrle_probabilisticBranching
  apply fslAdd_mono
  · exact fslMul_mono le_rfl h₁
  · exact fslMul_mono le_rfl h₂

theorem safeTuple_conditionalBranching
    ( h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c₁ ⦃[[P]]⦄)
    ( h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c₂ ⦃[[P]]⦄) :
    ⊢ [[RI]] ⦃⁅<e>⁆ ⬝ [[Q₁]] ⊔ ~⁅<e>⁆ ⬝ [[Q₂]]⦄
    if e then [[c₁]] else [[c₂]] fi ⦃[[P]]⦄ := by
  apply le_trans ?_ wrle_conditionalBranching
  rw [fslMax]
  apply sup_le_sup
  · exact fslMul_mono le_rfl h₁
  · exact fslMul_mono le_rfl h₂

theorem safeTuple_while (Q : StateRV Var)
    ( h_inv : inv ⊢ `[fsl| ⁅<e>⁆ ⬝ [[Q]] ⊔ ~⁅<e>⁆ ⬝ [[P]]])
    ( h_Q : ⊢ [[RI]] ⦃[[Q]]⦄ c ⦃[[inv]]⦄) :
    ⊢ [[RI]] ⦃[[inv]]⦄ while e begin [[c]] fi ⦃[[P]]⦄ :=
  wrle_while h_Q h_inv

theorem safeTuple_seq (Q₂ : StateRV Var)
    (h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c₁ ⦃[[Q₂]]⦄)
    (h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c₂ ⦃[[P]]⦄):
    ⊢ [[RI]] ⦃[[Q₁]]⦄ [[c₁]] ; [[c₂]] ⦃[[P]]⦄ :=
  le_trans (le_trans h₁ <| wrle_mono h₂) wrle_seq

theorem safeTuple_concur
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varRV P₂ ∪ varRV RI) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varRV P₁ ∪ varRV RI) = ∅)
    (h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c₁ ⦃[[P₁]]⦄)
    (h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c₂ ⦃[[P₂]]⦄) :
    ⊢ [[RI]] ⦃[[Q₁]] ⋆ [[Q₂]]⦄ [[c₁]] || [[c₂]] ⦃[[P₁]] ⋆ [[P₂]]⦄ :=
  le_trans (fslSepMul_mono h₁ h₂) (wrle_concur h_vars₁ h_vars₂)

theorem safeTuple_concur₃
    (h_vars₁  : wrtProg c₁ ∩ (varProg c₂ ∪ varProg c₃ ∪ varRV P₂ ∪ varRV P₃ ∪ varRV RI) = ∅)
    (h_vars₂  : wrtProg c₂ ∩ (varProg c₁ ∪ varProg c₃ ∪ varRV P₁ ∪ varRV P₃ ∪ varRV RI) = ∅)
    (h_vars₃  : wrtProg c₃ ∩ (varProg c₁ ∪ varProg c₂ ∪ varRV P₁ ∪ varRV P₂ ∪ varRV RI) = ∅)
    (h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c₁ ⦃[[P₁]]⦄)
    (h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c₂ ⦃[[P₂]]⦄)
    (h₃ : ⊢ [[RI]] ⦃[[Q₃]]⦄ c₃ ⦃[[P₃]]⦄) :
    ⊢ [[RI]]
    ⦃[[Q₁]] ⋆ [[Q₂]] ⋆ [[Q₃]]⦄
    [[c₁]] || [[c₂]] || [[c₃]]
    ⦃[[P₁]] ⋆ [[P₂]] ⋆ [[P₃]]⦄ := by
  apply safeTuple_concur
  · unfold varProg
    apply subset_antisymm ?_ (Set.empty_subset _)
    apply subset_trans
    · apply Set.inter_subset_inter le_rfl
      apply Set.union_subset_union ?_ le_rfl; swap
      apply Set.union_subset_union le_rfl ?_; swap
      apply varRV_of_fslSepMul
    · rw [← h_vars₁]
      rw [Set.union_assoc _ (varRV P₂) (varRV P₃)]
  · unfold wrtProg
    apply subset_antisymm ?_ (Set.empty_subset _)
    rw [Set.union_inter_distrib_right, ← Set.union_empty ∅]
    apply Set.union_subset_union
    · rw [← h_vars₂]
      apply Set.inter_subset_inter le_rfl
      apply Set.union_subset_union ?_ le_rfl
      rw [← Set.union_empty (varProg c₁ ∪ varRV P₁)]
      apply Set.union_subset_union ?_ (Set.empty_subset _)
      apply Set.union_subset_union ?_ le_rfl
      nth_rw 1 [← Set.union_empty (varProg c₁)]
      apply Set.union_subset_union le_rfl (Set.empty_subset _)
    · rw [← h_vars₃]
      apply Set.inter_subset_inter le_rfl
      apply Set.union_subset_union ?_ le_rfl
      rw [← Set.union_empty (varProg c₁ ∪ varRV P₁)]
      apply Set.union_subset_union ?_ (Set.empty_subset _)
      apply Set.union_subset_union ?_ le_rfl
      nth_rw 1 [← Set.union_empty (varProg c₁)]
      apply Set.union_subset_union le_rfl (Set.empty_subset _)
  · exact h₁
  apply safeTuple_concur
  · apply subset_antisymm ?_ (Set.empty_subset _)
    rw [← h_vars₂]
    apply Set.inter_subset_inter le_rfl
    apply Set.union_subset_union ?_ le_rfl
    apply Set.union_subset_union ?_ le_rfl
    nth_rw 1 [← Set.union_empty (varProg c₃)]
    apply Set.union_subset_union ?_ (Set.empty_subset _)
    nth_rw 1 [← Set.empty_union (varProg c₃)]
    apply Set.union_subset_union (Set.empty_subset _) le_rfl
  · apply subset_antisymm ?_ (Set.empty_subset _)
    rw [← h_vars₃]
    apply Set.inter_subset_inter le_rfl
    apply Set.union_subset_union ?_ le_rfl
    apply Set.union_subset_union ?_ le_rfl
    nth_rw 1 [← Set.union_empty (varProg c₂)]
    apply Set.union_subset_union ?_ (Set.empty_subset _)
    nth_rw 1 [← Set.empty_union (varProg c₂)]
    apply Set.union_subset_union (Set.empty_subset _) le_rfl
  · exact h₂
  · exact h₃

theorem safeTuple_atom
    (h_atom : atomicProgram c)
    (h : ⊢ emp ⦃[[Q]] ⋆ [[RI]]⦄ c ⦃[[P]] ⋆ [[RI]]⦄) :
    ⊢ [[RI]] ⦃[[Q]]⦄ c ⦃[[P]]⦄ :=
  wrle_atom h h_atom

theorem safeTuple_share
    (h : ⊢ [[RI₁]] ⋆ [[RI₂]] ⦃[[Q]]⦄ c ⦃[[P]]⦄) :
    ⊢ [[RI₁]] ⦃[[Q]] ⋆ [[RI₂]]⦄ c ⦃[[P]] ⋆ [[RI₂]]⦄ :=
  wrle_share h

theorem safeTuple_frame
    (h_cut_free : (wrtProg c) ∩ (varRV F) = ∅)
    (h : ⊢ [[RI]] ⦃[[Q]]⦄ c ⦃[[P]]⦄) :
    ⊢ [[RI]] ⦃[[Q]] ⋆ [[F]]⦄ c ⦃[[P]] ⋆ [[F]]⦄ :=
  le_trans (fslSepMul_mono h le_rfl) (wrle_frame h_cut_free)

theorem safeTuple_monotonicty
    ( Q' P' : StateRV Vars)
    (h₁ : Q ⊢ Q') (h₂ : P' ⊢ P)
    (h : ⊢ [[RI]] ⦃[[Q']]⦄ c ⦃[[P']]⦄) :
    ⊢ [[RI]] ⦃[[Q]]⦄ c ⦃[[P]]⦄ :=
  le_trans h₁ <| le_trans h <| wrle_mono h₂

theorem safeTuple_max
    (h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c ⦃[[P₁]]⦄)
    (h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c ⦃[[P₂]]⦄) :
    ⊢ [[RI]] ⦃[[Q₁]] ⊔ [[Q₂]]⦄ c ⦃[[P₁]] ⊔ [[P₂]]⦄ := by
  apply le_trans ?_ wrle_max
  rw [fslMax]
  exact sup_le_sup h₁ h₂

theorem safeTuple_weightedSum
    (h_precise : precise RI) (h_vars : (wrtProg c) ∩ (varRV (fslReal e)) = ∅)
    (h₁ : ⊢ [[RI]] ⦃[[Q₁]]⦄ c ⦃[[P₁]]⦄) (h₂ : ⊢ [[RI]] ⦃[[Q₂]]⦄ c ⦃[[P₂]]⦄) :
    ⊢ [[RI]] ⦃<e> ⬝ [[Q₁]] + ~<e> ⬝ [[Q₂]]⦄ c ⦃<e> ⬝ [[P₁]] + ~<e> ⬝ [[P₂]]⦄ := by
  apply le_trans ?_ (wrle_weightedSum h_precise h_vars)
  exact fslAdd_mono (fslMul_mono le_rfl h₁) (fslMul_mono le_rfl h₂)

theorem safeTuple_false_left :
    ⊢ [[RI]] ⦃ fFalse ⦄ c ⦃ [[P]] ⦄ := by
  exact fslFalse_le _

end CFSL
