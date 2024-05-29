

class Entailment (α : Type u) where
  entail : α → α → Prop

infix:50 " ⊢ "  => Entailment.entail
