import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

open scoped Topology Classical

variable {α β : Type*}
variable [AddCommMonoid α] [TopologicalSpace α] {f : β → α}

theorem tsum_pair {b₁ b₂ : β} (f : β → α) (h : b₁ ≠ b₂) :
    ∑' x : ({b₁, b₂} : Set β), f x = f b₁ + f b₂ := by
  rw [← Finset.coe_pair, Finset.tsum_subtype', Finset.sum_pair h]

end
