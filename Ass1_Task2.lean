theorem dm_pred : (∀ x : A, (¬ PP x ∧ ¬ QQ x)) → ¬ (∃ x : A, (PP x ∨ QQ x)) :=
begin
  -- We assume that the left side of the implication is true 
  assume h,

  -- We also assume the right side is true
  assume h2,

  -- Cases on h2 extracts "a" as the specific x, and "ha" as PP a ∨ QQ a
  cases h2 with a ha,

  -- We know every x has neither PP nor QQ, apply that to "a"
  -- this gives us both ¬PP a and ¬QQ a
  have hna := h a,
  cases hna with npa nqa,

  -- "a" has PP or QQ, split into both cases
  cases ha with ppa qqa,

  -- Case 1: a has PP, but we also have ¬PP a, direct contradiction
  exact npa ppa,

  -- Case 2: a has QQ, but we also have ¬QQ a, direct contradiction
  exact nqa qqa,

end
