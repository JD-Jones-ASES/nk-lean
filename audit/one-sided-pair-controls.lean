import NK.OneSidedPairMoment

open NK

example : (((10 * 10 / 21 : ℕ) : ℝ) / 10) ≤ (2 : ℝ)⁻¹ :=
  OneSidedPairMoment.reciprocal_lower 10 21 2 (by decide) (by norm_num) (by norm_num)

example : OneSidedPairMoment.WidthValid 1000000 2 1 2 1 := by decide +kernel
example : ¬ OneSidedPairMoment.WidthValid 1000000 2 1 0 1 := by decide +kernel
example : ¬ OneSidedPairMoment.WidthValid 1000000 2 1 2 0 := by decide +kernel
example : ¬ OneSidedPairMoment.WidthValid 1000000 2 100 1 1 := by decide +kernel

-- The separate positive-scale premise is essential and remains in every soundness theorem.
example : OneSidedPairMoment.WidthValid 0 2 1 2 1 := by decide +kernel
example : ¬ PairMomentCertificate.WidthValid 0 2 1 2 1 := by decide +kernel

example : ((PairMomentCertificate.widthBounds 1000000 2 1 2 1).lo : ℝ) / 1000000 ≤
    ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    (OneSidedPairMoment.width_lower 1000000 2 1 2 1 (by decide) (by decide +kernel))

private def miniTree : PairCertificateTree := .leaf ⟨([0], [0]), 0, 1⟩

example : (1 : ℝ) ^ (0 / 1 : ℝ) ≤ (2 : ℝ) *
    (miniTree.rows.map (fun r => ((r.width : ℝ) / 2) ^ (1 / 2 : ℝ))).sum := by
  simpa only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] using
    (OneSidedPairMoment.moment_bound 1000000 2 1 2 1 2 0 1 miniTree
      ⟨0, 0, 1000000, 1000001⟩ (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))

example : ¬ ((⟨0, 0, 1000000, 999999⟩ : RationalMomentCertificate.PowerData).Valid
    1000000 1 1 0 1) := by decide +kernel

#print axioms NK.OneSidedPairMoment.reciprocal_lower
#print axioms NK.OneSidedPairMoment.width_lower
#print axioms NK.OneSidedPairMoment.lowerSum_sound
#print axioms NK.OneSidedPairMoment.moment_bound
