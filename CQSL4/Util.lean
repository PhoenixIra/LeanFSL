

theorem not_none_option_of_some_option (o : Option α) (a : α) (h : o = some a) : o ≠ none := by
  intro h_none
  cases o with
  | none => simp only at h
  | some a' => simp only at h_none
