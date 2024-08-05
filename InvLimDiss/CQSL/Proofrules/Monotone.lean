import InvLimDiss.CQSL.WeakExpectation


namespace CQSL

theorem wrle_step_mono_of_parameters_of_le_RV (h_le : P s ≤ Q s) :
    wrle_step P resource X c s ≤ wrle_step Q resource X c s := by
  simp only [wrle_step]
  split
  case h_1 => exact h_le
  case h_2 => rfl
  case h_3 => rfl

theorem wrle_step_mono_of_le_RV (h_le : P ≤ Q) :
    wrle_step P resource ≤ wrle_step Q resource := by
  intro X c s
  apply wrle_step_mono_of_parameters_of_le_RV
  exact h_le s

theorem wrle_mono (h : P ≤ Q) :
    `[qsl| wrle [c] ([[P]]|[[resource]]) ⊢ wrle [c] ([[Q]]|[[resource]])] := sorry



end CQSL
