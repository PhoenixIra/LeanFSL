/-!
  This file only contains a syntax typeclass for entailments, in order to allow both
  quantitative and qualitative separation logic to use the same symbol.
-/

class Entailment (α : Type u) where
  entail : α → α → Prop

infix:50 " ⊢ "  => Entailment.entail
