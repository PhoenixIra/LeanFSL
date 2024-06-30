import InvLimDiss.CQSL.Step
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.AtomicFinal
import Mathlib.Order.FixedPoints


namespace CQSL

open QSL Syntax OrderHom unitInterval

variable {Var : Type}

noncomputable def wrlp_step (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[qsl| qFalse]
  | X, program => `[qsl| [[resource]] -⋆ [[step program (fun c => `[qsl| [[X c]] ⋆ [[resource]] ]) ]] ]

theorem wrlp_monotone (post : StateRV Var) (resource : StateRV Var) : Monotone (wrlp_step post resource) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro c
  unfold wrlp_step
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply monotone_qslSepImp le_rfl
    apply monotone_step
    rw [Pi.le_def]
    intro c
    rw [Pi.le_def]
    intro s
    apply monotone_qslSepCon
    · rw [Pi.le_def] at h_X
      exact h_X c
    · exact le_rfl

noncomputable def wrlp' (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :=
  gfp ⟨wrlp_step post resource, wrlp_monotone post resource⟩ program

syntax "wrlp [" term "] (" qsl " | " qsl ")" : qsl
macro_rules
  | `(term| `[qsl| wrlp [$c:term] ($p:qsl | $r:qsl)]) => `(wrlp' $c `[qsl| $p] `[qsl| $r])
  | `(term| `[qsl $v| wrlp [$c:term] ($p:qsl | $r:qsl)]) => `(wrlp' $c `[qsl $v| $p] `[qsl $v| $r])

open Lean PrettyPrinter Delaborator

def makeBrackets [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => `(qsl| ( $f ) )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander wrlp']
def unexpanderWrlp : Unexpander
  | `($_ $c:term $p $r) =>
      do `(`[qsl| wrlp [$c:term] ($(← makeBrackets p):qsl | $(← makeBrackets r):qsl )])
  | _ => throw ()


theorem wrlp_unroll (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :
    `[qsl| wrlp [program] ([[post]] | [[resource]])] = match program with
  | [Prog| ↓ ] => post
  | [Prog| ↯ ] => `[qsl| qFalse]
  | program => `[qsl| [[resource]] -⋆ [[step program
    (fun c => `[qsl| wrlp [c] ([[post]] | [[resource]]) ⋆ [[resource]] ]) ]] ] := by sorry

theorem wrlp_atom (h : `[qsl| [[P]] ⋆ [[resource]] ⊢ wrlp [c] ([[P]] ⋆ [[resource]] | emp)])
    (h_atom : c ∈ atomicProgram):
    `[qsl| [[P]] ⊢ wrlp [c] ([[P]] | emp)] := by sorry

theorem wrlp_skip : `[qsl| [[P]] ⊢ wrlp [ [Prog| skip] ] ([[P]] | [[RI]])] := by
  rw [wrlp_unroll]
  split
  case h_1 h_eq => cases h_eq
  case h_2 h_eq => cases h_eq
  case h_3 h_ne_abt h_ne_term =>
    sorry



end CQSL
