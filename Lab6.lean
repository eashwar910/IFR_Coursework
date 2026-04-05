variables (A : Type) (PP QQ : A → Prop)
constant raa : ∀ {P : Prop}, ¬¬P → P
constant em  : ∀ (P : Prop), P ∨ ¬P

-- We are given that "not every x has property PP"
-- Our goal is to prove that "some x exists that does not have PP"

theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin

  assume h,

  -- We assume that the left side of the implication is true 
  -- and our new goal is to prove the right side. 
  -- Instead of finding x directly, let's prove by contradiction
  -- We assume the opposite: "no x exists without PP", and show that breaks everything
  apply raa,
  assume h2,

  -- Now, we try to clash the two assumotions
  -- To crash into h, we need to prove "every x HAS PP" (which h says is false)
  -- Once we prove "everyone has PP", it contradicts h and we get our false
  apply h,

  -- To prove "every x has PP", pick one random x called a and prove it for that
  -- If it works for a random a, it works for everyone
  assume a,

  -- Does this specific a have PP or not? Has to be one or the other
  cases em (PP a) with pa npa,

  { -- Case 1: a HAS property PP
    -- That's exactly what we needed to prove, so we're done here
    exact pa },

  { -- Case 2: a does NOT have property PP
    -- It clashes here
    -- We're going to manufacture a contradiction (false)
    have f : false,
    { -- h2 says "no x exists without PP"
      -- to crash into h2, we need to show "some x exists without PP"
      apply h2,
      -- a is our witness! we point at a and say "THIS ONE doesn't have PP"
      existsi a,
      -- and here's the proof that a doesn't have PP (we got this from the case split)
      exact npa },
    -- we now have false in our hands
    -- anything follows from false, so the goal is closed
    cases f },
end