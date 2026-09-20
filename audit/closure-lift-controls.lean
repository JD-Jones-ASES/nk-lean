import NK.ClosureLift

#print axioms NK.powerArc_mod_perfectPowerClosure
#print axioms NK.IntervalAlphabet.closureLift
#print axioms NK.IntervalAlphabet.closureLift_card
#print axioms NK.IntervalAlphabet.closureLift_moment

private theorem closure_six_nine : NK.perfectPowerClosure 6 9 = 729 := by
  have h := NK.perfectPowerClosure_prime_pow 6 3 2 (by decide) (by decide)
  norm_num at h
  exact h

example (A : NK.IntervalAlphabet 6 9) :
    (A.closureLift (by decide) (by decide)).support.card = 81 * A.support.card := by
  simpa [closure_six_nine] using A.closureLift_card (by decide) (by decide)

-- No sign restriction on the moment exponent is needed for a copying identity.
example (A : NK.IntervalAlphabet 6 9) (f : ℝ) :
    (A.closureLift (by decide) (by decide)).moment f = 81 * A.moment f := by
  simpa [closure_six_nine] using A.closureLift_moment (by decide) (by decide) f

-- A complete fiber count including the endpoint residue.
example : ((Finset.range 12).filter fun x => x % 4 ∈ ({0, 3} : Finset ℕ)).card = 6 := by decide

-- Overlifting d=4 to16 would create an arc inside a single seed fiber.
example : NK.PowerArc 2 16 0 4 ∧ (0 : ℕ) % 4 = 4 % 4 := by
  refine ⟨⟨by decide, 2, by decide⟩, by decide⟩
example : ¬ NK.PowerArc 2 4 ((0 : ℕ) % 4) (4 % 4) := by
  intro h
  exact h.1 (by decide)
