import InvLimDiss.CFSL.Proofrules

namespace CFSL

open FSL Syntax

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

theorem safeTuple_assign (P : StateRV Var) (h : x ∉ varRV RI) : ⊢ [[RI]] ⦃[[P]](x ↦ e)⦄ x ≔ e ⦃[[P]]⦄ :=
    wrle_assign h

theorem safeTuple_assign (P : StateRV Var) (h : x ∉ varRV RI) : ⊢ [[RI]] ⦃[[P]](x ↦ e)⦄ x ≔ e ⦃[[P]]⦄ :=




end CFSL
