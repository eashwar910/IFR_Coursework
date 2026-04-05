open bool
local notation ! := bnot

-- For any boolean x, double negation gives back the original value
-- i.e flipping a boolean twice always returns to where you started

lemma ex7q03 : ∀ x : bool, x = !(!x) :=
begin

  -- use an arbitrary boolean x, our goal is to prove x = !(!x) for this x
  assume x,

  -- since x is a bool, it can ONLY be tt or ff
  -- so we just check both cases manually and verify each one works

  cases x,

  -- Case 1: x = ff (false)
  -- lets trace through what !(!ff) actually computes to:
  -- !ff = tt        (flipping false gives true)
  -- !tt = ff        (flipping true gives false)
  -- so !(!ff) = ff which is exactly x
  -- both sides are ff so they are equal

  refl,

  -- Case 2: x = tt (true)
  -- lets trace through what !(!tt) actually computes to:
  -- !tt = ff        (flipping true gives false)
  -- !ff = tt        (flipping false gives true)
  -- so !(!tt) = tt which is exactly x
  -- both sides are tt so they are equal
  
  refl,

end