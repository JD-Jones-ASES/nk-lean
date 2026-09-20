import NK.NumericBounds

/-! # Sound composition and range reduction for numerical certificates

The shift and reduced argument can be supplied by a rational certificate;
the identities and interval hypotheses below are checked independently.
Existence lemmas establish that these reductions cover every positive
logarithm argument and every nonnegative exponential argument. They do not
claim to verify a particular bit-length or halving implementation.

For logarithms, `NumericBounds.log_unit_bounds` uses the larger Mathlib
atanh tail, without the sharper factor `1/(2*n+1)`.
Generated certificates must use that proved larger tail unless
the sharper remainder is separately proved. Fixed-point rounding remains
outside this module.
-/

namespace NK.NumericReduction

/-- Every positive real has a signed dyadic normalization to [1,2). -/
theorem exists_log_dyadic (x : ℝ) (hx : 0 < x) :
    ∃ s : ℤ, ∃ u : ℝ, x = (2 : ℝ) ^ s * u ∧ 1 ≤ u ∧ u < 2 := by
  obtain ⟨s, hslo, hshi⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ s := zpow_pos (by norm_num) s
  refine ⟨s, x / (2 : ℝ) ^ s, ?_, ?_, ?_⟩
  · field_simp
  · exact (le_div_iff₀ hp).mpr (by simpa using hslo)
  · apply (div_lt_iff₀ hp).mpr
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at hshi
    simpa [mul_comm] using hshi

/-- Positive rational inputs admit a rational reduced argument as well. -/
theorem exists_log_dyadic_rat (x : ℚ) (hx : 0 < x) :
    ∃ s : ℤ, ∃ u : ℚ, x = (2 : ℚ) ^ s * u ∧ 1 ≤ u ∧ u < 2 := by
  obtain ⟨s, hslo, hshi⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℚ) < 2)
  have hp : (0 : ℚ) < 2 ^ s := zpow_pos (by norm_num) s
  refine ⟨s, x / (2 : ℚ) ^ s, ?_, ?_, ?_⟩
  · field_simp
  · exact (le_div_iff₀ hp).mpr (by simpa using hslo)
  · apply (div_lt_iff₀ hp).mpr
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one] at hshi
    simpa [mul_comm] using hshi

/-- Signed dyadic reduction of a real logarithm. -/
theorem log_dyadic (s : ℤ) (u : ℝ) (hu : 0 < u) :
    Real.log ((2 : ℝ) ^ s * u) = (s : ℝ) * Real.log 2 + Real.log u := by
  rw [Real.log_mul (zpow_ne_zero s (by norm_num)) hu.ne', Real.log_zpow]

/-- The same identity accepts an exact rational decomposition. -/
theorem log_rat_dyadic (x u : ℚ) (s : ℤ) (hu : 0 < u)
    (hxu : x = (2 : ℚ) ^ s * u) :
    Real.log (x : ℝ) = (s : ℝ) * Real.log 2 + Real.log (u : ℝ) := by
  rw [hxu]
  push_cast
  exact log_dyadic s (u : ℝ) (by exact_mod_cast hu)

/-- Multiplication by a negative shift reverses the enclosure endpoints. -/
def shiftLower (s : ℤ) (l h : ℝ) : ℝ :=
  if 0 ≤ s then (s : ℝ) * l else (s : ℝ) * h

/-- Upper endpoint paired with `shiftLower`. -/
def shiftUpper (s : ℤ) (l h : ℝ) : ℝ :=
  if 0 ≤ s then (s : ℝ) * h else (s : ℝ) * l

theorem shift_bounds (s : ℤ) (x l h : ℝ) (hl : l ≤ x) (hh : x ≤ h) :
    shiftLower s l h ≤ (s : ℝ) * x ∧ (s : ℝ) * x ≤ shiftUpper s l h := by
  by_cases hs : 0 ≤ s
  · have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
    simp only [shiftLower, shiftUpper, if_pos hs]
    exact ⟨mul_le_mul_of_nonneg_left hl hsR, mul_le_mul_of_nonneg_left hh hsR⟩
  · have hsR : (s : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hs))
    simp only [shiftLower, shiftUpper, if_neg hs]
    exact ⟨mul_le_mul_of_nonpos_left hh hsR, mul_le_mul_of_nonpos_left hl hsR⟩

/-- Combine certified enclosures of log2 and of the reduced logarithm,
including negative dyadic shifts. -/
theorem log_dyadic_bounds (s : ℤ) (u l2 h2 lu hu : ℝ) (hupos : 0 < u)
    (hl2 : l2 ≤ Real.log 2) (hh2 : Real.log 2 ≤ h2)
    (hlu : lu ≤ Real.log u) (hhu : Real.log u ≤ hu) :
    shiftLower s l2 h2 + lu ≤ Real.log ((2 : ℝ) ^ s * u) ∧
      Real.log ((2 : ℝ) ^ s * u) ≤ shiftUpper s l2 h2 + hu := by
  rw [log_dyadic s u hupos]
  have hs := shift_bounds s (Real.log 2) l2 h2 hl2 hh2
  exact ⟨add_le_add hs.1 hlu, add_le_add hs.2 hhu⟩

/-- Reciprocal arguments negate a logarithm and swap its two endpoints. -/
theorem log_inv_bounds (x l h : ℝ) (hl : l ≤ Real.log x) (hh : Real.log x ≤ h) :
    -h ≤ Real.log x⁻¹ ∧ Real.log x⁻¹ ≤ -l := by
  rw [Real.log_inv]
  exact ⟨neg_le_neg hh, neg_le_neg hl⟩

/-- Every nonnegative real exponential argument can be reduced to [0,1/8]. -/
theorem exists_exp_dyadic (t : ℝ) (ht : 0 ≤ t) :
    ∃ m : ℕ, ∃ u : ℝ, t = (2 : ℝ) ^ m * u ∧ 0 ≤ u ∧ u ≤ 1 / 8 := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (8 * t) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) m
  refine ⟨m, t / (2 : ℝ) ^ m, ?_, div_nonneg ht hp.le, ?_⟩
  · field_simp
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- Rational exponential arguments retain a rational reduced argument. -/
theorem exists_exp_dyadic_rat (t : ℚ) (ht : 0 ≤ t) :
    ∃ m : ℕ, ∃ u : ℚ, t = (2 : ℚ) ^ m * u ∧ 0 ≤ u ∧ u ≤ 1 / 8 := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (8 * t) (by norm_num : (1 : ℚ) < 2)
  have hp : (0 : ℚ) < 2 ^ m := pow_pos (by norm_num) m
  refine ⟨m, t / (2 : ℚ) ^ m, ?_, div_nonneg ht hp.le, ?_⟩
  · field_simp
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- The exact identity behind repeated squaring after dyadic reduction. -/
theorem exp_dyadic (u : ℝ) (m : ℕ) :
    Real.exp ((2 : ℝ) ^ m * u) = (Real.exp u) ^ (2 ^ m) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using Real.exp_nat_mul u (2 ^ m)

/-- Propagate a nonnegative lower endpoint and an exponential enclosure
through any number of exact squarings. -/
theorem exp_dyadic_bounds (u l h : ℝ) (m : ℕ) (hl0 : 0 ≤ l)
    (hl : l ≤ Real.exp u) (hh : Real.exp u ≤ h) :
    l ^ (2 ^ m) ≤ Real.exp ((2 : ℝ) ^ m * u) ∧
      Real.exp ((2 : ℝ) ^ m * u) ≤ h ^ (2 ^ m) := by
  rw [exp_dyadic]
  exact ⟨pow_le_pow_left₀ hl0 hl _, pow_le_pow_left₀ (Real.exp_pos u).le hh _⟩

/-- Inverting a positive enclosure gives an enclosure of the negative exponential. -/
theorem exp_neg_bounds (u l h : ℝ) (hl0 : 0 < l)
    (hl : l ≤ Real.exp u) (hh : Real.exp u ≤ h) :
    1 / h ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ 1 / l := by
  rw [Real.exp_neg, ← one_div]
  exact ⟨one_div_le_one_div_of_le (Real.exp_pos u) hh,
    one_div_le_one_div_of_le hl0 hl⟩

/-- Combined repeated squaring and inversion, with the endpoint reversal explicit. -/
theorem exp_neg_dyadic_bounds (u l h : ℝ) (m : ℕ) (hl0 : 0 < l)
    (hl : l ≤ Real.exp u) (hh : Real.exp u ≤ h) :
    1 / h ^ (2 ^ m) ≤ Real.exp (-((2 : ℝ) ^ m * u)) ∧
      Real.exp (-((2 : ℝ) ^ m * u)) ≤ 1 / l ^ (2 ^ m) := by
  have hs := exp_dyadic_bounds u l h m hl0.le hl hh
  exact exp_neg_bounds _ _ _ (pow_pos hl0 _) hs.1 hs.2

end NK.NumericReduction
