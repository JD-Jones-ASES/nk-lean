import NK.BlockComposition
import NK.AlphabetSymmetries
import Mathlib.Analysis.Subadditive

/-! # Binary square interval capacity

`U f m` is the supremum of moments of actual finite interval alphabets modulo
4^m. The results below assume f≥0. Level zero is included as modulus1, so its
normalization is proved from alphabets rather than imposed by a recurrence.
-/
namespace NK.BinaryCapacity

/-- The moments attained by finite alphabets at one binary depth. -/
def momentSet (f : ℝ) (m : ℕ) : Set ℝ :=
  {z | ∃ A : IntervalAlphabet 2 (4 ^ m), A.moment f = z}

/-- Supremum capacity at a finite depth. Use at nonnegative moment exponents. -/
noncomputable def U (f : ℝ) (m : ℕ) : ℝ := sSup (momentSet f m)

theorem moment_nonneg {k M : ℕ} (A : IntervalAlphabet k M) (f : ℝ) : 0 ≤ A.moment f := by
  apply Finset.sum_nonneg
  intro a _
  exact Real.rpow_nonneg (A.interval a.val a.property).width_pos.le f

/-- Widths at most one give the elementary finite-residue upper bound. -/
theorem moment_le_modulus {k M : ℕ} (A : IntervalAlphabet k M) (f : ℝ) (hf : 0 ≤ f) :
    A.moment f ≤ (M : ℝ) := by
  have hsum : A.moment f ≤ (A.support.card : ℝ) := by
    unfold IntervalAlphabet.moment
    calc
      _ ≤ ∑ _a ∈ A.support.attach, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        have h := Real.rpow_le_rpow (A.interval a.val a.property).width_pos.le
          (A.interval a.val a.property).width_le_one hf
        simpa only [Real.one_rpow] using h
      _ = _ := by simp
  have hsub : A.support ⊆ Finset.range M := fun x hx => Finset.mem_range.mpr (A.residue_lt x hx)
  have hcard : A.support.card ≤ M := by simpa using Finset.card_le_card hsub
  exact hsum.trans (by exact_mod_cast hcard)

theorem momentSet_nonempty (f : ℝ) (m : ℕ) : (momentSet f m).Nonempty :=
  ⟨0, IntervalAlphabet.empty 2 (4 ^ m), IntervalAlphabet.empty_moment _ _ _⟩

theorem momentSet_bddAbove (f : ℝ) (hf : 0 ≤ f) (m : ℕ) : BddAbove (momentSet f m) := by
  refine ⟨(4 : ℝ)^m, ?_⟩
  rintro z ⟨A, rfl⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using moment_le_modulus A f hf

theorem moment_le_U (f : ℝ) (hf : 0 ≤ f) (m : ℕ) (A : IntervalAlphabet 2 (4 ^ m)) :
    A.moment f ≤ U f m := le_csSup (momentSet_bddAbove f hf m) ⟨A, rfl⟩

theorem U_le_four_pow (f : ℝ) (hf : 0 ≤ f) (m : ℕ) : U f m ≤ (4 : ℝ)^m := by
  apply csSup_le (momentSet_nonempty f m)
  rintro z ⟨A, rfl⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using moment_le_modulus A f hf

theorem one_le_U (f : ℝ) (hf : 0 ≤ f) (m : ℕ) : 1 ≤ U f m := by
  have h := moment_le_U f hf m (IntervalAlphabet.singleton 2 (4 ^ m) 0 (by positivity) UnitInterval.unit)
  simpa only [IntervalAlphabet.singleton_moment, UnitInterval.unit, Real.one_rpow] using h

theorem U_pos (f : ℝ) (hf : 0 ≤ f) (m : ℕ) : 0 < U f m := lt_of_lt_of_le zero_lt_one (one_le_U f hf m)

@[simp] theorem U_zero (f : ℝ) (hf : 0 ≤ f) : U f 0 = 1 := by
  apply le_antisymm
  · simpa using U_le_four_pow f hf 0
  · exact one_le_U f hf 0

private theorem four_pow_square (m : ℕ) : 4 ^ m = (2 ^ m) ^ 2 := by
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
  norm_num

/-- A product of two attained moments is attained at the sum of their depths. -/
theorem exists_product_alphabet (f : ℝ) (m n : ℕ)
    (A : IntervalAlphabet 2 (4 ^ m)) (B : IntervalAlphabet 2 (4 ^ n)) :
    ∃ C : IntervalAlphabet 2 (4 ^ (m+n)), C.moment f = A.moment f * B.moment f := by
  rw [pow_add]
  exact ⟨BlockComposition.nested A B (2 ^ m) (by positivity) (by positivity) (four_pow_square m),
    BlockComposition.nested_moment A B (2 ^ m) (by positivity) (by positivity) (four_pow_square m) f⟩

theorem moment_product_le_U (f : ℝ) (hf : 0 ≤ f) (m n : ℕ)
    (A : IntervalAlphabet 2 (4 ^ m)) (B : IntervalAlphabet 2 (4 ^ n)) :
    A.moment f * B.moment f ≤ U f (m+n) := by
  obtain ⟨C, hC⟩ := exists_product_alphabet f m n A B
  rw [← hC]
  exact moment_le_U f hf (m+n) C

/-- Supremum supermultiplicativity follows from actual block products. -/
theorem U_supermultiplicative (f : ℝ) (hf : 0 ≤ f) (m n : ℕ) :
    U f m * U f n ≤ U f (m+n) := by
  have hnpos := U_pos f hf n
  have hprod : ∀ A : IntervalAlphabet 2 (4 ^ m), A.moment f * U f n ≤ U f (m+n) := by
    intro A
    by_cases hz : A.moment f = 0
    · rw [hz, zero_mul]
      exact (U_pos f hf (m+n)).le
    · have hApos : 0 < A.moment f := lt_of_le_of_ne (moment_nonneg A f) (Ne.symm hz)
      have hs : U f n ≤ U f (m+n) / A.moment f := by
        apply csSup_le (momentSet_nonempty f n)
        rintro z ⟨B, rfl⟩
        apply (le_div_iff₀ hApos).mpr
        simpa only [mul_comm] using moment_product_le_U f hf m n A B
      have h := (le_div_iff₀ hApos).mp hs
      simpa only [mul_comm] using h
  apply (le_div_iff₀ hnpos).mp
  apply csSup_le (momentSet_nonempty f m)
  rintro z ⟨A, rfl⟩
  exact (le_div_iff₀ hnpos).mpr (hprod A)

private theorem square_mod_four (z : ℕ) : (z*z) % 4 = 0 ∨ (z*z) % 4 = 1 := by
  have h : z % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mul_mod]
  interval_cases z % 4 <;> norm_num

/-- The two independent base-four digits0 and2 carry full-width intervals. -/
def baseIndependent : IntervalAlphabet 2 4 where
  support := {0, 2}
  residue_lt x hx := by simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega
  interval _ _ := UnitInterval.unit
  ordered x hx y hy harc := by
    obtain ⟨hne, z, hz⟩ := harc
    have hx' : x = 0 ∨ x = 2 := by simpa using hx
    have hy' : y = 0 ∨ y = 2 := by simpa using hy
    have hroot := square_mod_four z
    have hz' : (x % 4 + (z*z) % 4) % 4 = y % 4 := by
      rw [pow_two, Nat.add_mod] at hz
      exact hz
    omega

@[simp] theorem baseIndependent_moment (f : ℝ) : baseIndependent.moment f = 2 := by
  change (∑ _a ∈ ({0, 2} : Finset ℕ).attach, (1 : ℝ)^f) = 2
  simp only [Real.one_rpow, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
  norm_num

theorem two_le_U_one (f : ℝ) (hf : 0 ≤ f) : 2 ≤ U f 1 := by
  have h := moment_le_U f hf 1 baseIndependent
  simpa only [baseIndependent_moment] using h

/-- Repeated actual independent blocks give2^m, including the normalized level0. -/
theorem two_pow_le_U (f : ℝ) (hf : 0 ≤ f) (m : ℕ) : (2 : ℝ)^m ≤ U f m := by
  induction m with
  | zero => simpa only [pow_zero] using one_le_U f hf 0
  | succ m ih =>
    calc
      (2 : ℝ)^(m+1) = (2 : ℝ)^m * 2 := pow_succ _ _
      _ ≤ U f m * U f 1 := mul_le_mul ih (two_le_U_one f hf) (by positivity) (U_pos f hf m).le
      _ ≤ U f (m+1) := U_supermultiplicative f hf m 1

/-- The normalized finite-depth growth factor; depth zero is harmlessly1. -/
noncomputable def growth (f : ℝ) (m : ℕ) : ℝ := U f m ^ (1 / (m : ℝ))

theorem log_U_bounds (f : ℝ) (hf : 0 ≤ f) (m : ℕ) :
    (m : ℝ) * Real.log 2 ≤ Real.log (U f m) ∧
    Real.log (U f m) ≤ (m : ℝ) * Real.log 4 := by
  constructor
  · have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^m) (two_pow_le_U f hf m)
    simpa only [Real.log_pow] using h
  · have h := Real.log_le_log (U_pos f hf m) (U_le_four_pow f hf m)
    simpa only [Real.log_pow] using h

theorem log_rate_bounds (f : ℝ) (hf : 0 ≤ f) (m : ℕ) (hm : 1 ≤ m) :
    Real.log 2 ≤ Real.log (U f m) / (m : ℝ) ∧
    Real.log (U f m) / (m : ℝ) ≤ Real.log 4 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := log_U_bounds f hf m
  constructor
  · apply (le_div_iff₀ hmpos).mpr
    simpa only [mul_comm] using h.1
  · apply (div_le_iff₀ hmpos).mpr
    simpa only [mul_comm] using h.2

theorem growth_eq_exp (f : ℝ) (hf : 0 ≤ f) (m : ℕ) :
    growth f m = Real.exp (Real.log (U f m) / (m : ℝ)) := by
  rw [growth, Real.rpow_def_of_pos (U_pos f hf m)]
  congr 1
  ring

theorem growth_bounds (f : ℝ) (hf : 0 ≤ f) (m : ℕ) (hm : 1 ≤ m) :
    2 ≤ growth f m ∧ growth f m ≤ 4 := by
  rw [growth_eq_exp f hf m]
  have h := log_rate_bounds f hf m hm
  constructor
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr h.1
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using Real.exp_le_exp.mpr h.2

private theorem neg_log_subadditive (f : ℝ) (hf : 0 ≤ f) :
    Subadditive (fun m => -Real.log (U f m)) := by
  intro m n
  have h := Real.log_le_log (mul_pos (U_pos f hf m) (U_pos f hf n))
    (U_supermultiplicative f hf m n)
  rw [Real.log_mul (U_pos f hf m).ne' (U_pos f hf n).ne'] at h
  linarith

private theorem neg_log_rate_bddBelow (f : ℝ) (hf : 0 ≤ f) :
    BddBelow (Set.range (fun m : ℕ => -Real.log (U f m) / (m : ℝ))) := by
  refine ⟨-Real.log 4, ?_⟩
  rintro z ⟨m, rfl⟩
  change -Real.log 4 ≤ -Real.log (U f m) / (m : ℝ)
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, div_zero]
    exact neg_nonpos.mpr (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  · have h := (log_rate_bounds f hf m (by omega)).2
    rw [neg_div]
    exact neg_le_neg h

/-- Fekete applied to negative logarithms gives a genuine limit, and every
positive-depth growth factor lies below it. -/
theorem exists_growth_limit (f : ℝ) (hf : 0 ≤ f) :
    ∃ L : ℝ, 2 ≤ L ∧ L ≤ 4 ∧
      Filter.Tendsto (growth f) Filter.atTop (nhds L) ∧
      ∀ m : ℕ, 1 ≤ m → growth f m ≤ L := by
  let hsub := neg_log_subadditive f hf
  have hbdd := neg_log_rate_bddBelow f hf
  have ht : Filter.Tendsto (fun m : ℕ => Real.log (U f m) / (m : ℝ))
      Filter.atTop (nhds (-hsub.lim)) := by
    simpa only [neg_div, neg_neg] using (hsub.tendsto_lim hbdd).neg
  have htExp : Filter.Tendsto (growth f) Filter.atTop (nhds (Real.exp (-hsub.lim))) := by
    have h := (Real.continuous_exp.tendsto (-hsub.lim)).comp ht
    simpa only [Function.comp_def, ← growth_eq_exp f hf] using h
  refine ⟨Real.exp (-hsub.lim), ?_, ?_, htExp, ?_⟩
  · apply ge_of_tendsto htExp
    exact Filter.eventually_atTop.mpr ⟨1, fun m hm => (growth_bounds f hf m hm).1⟩
  · apply le_of_tendsto htExp
    exact Filter.eventually_atTop.mpr ⟨1, fun m hm => (growth_bounds f hf m hm).2⟩
  · intro m hm
    rw [growth_eq_exp f hf m]
    apply Real.exp_le_exp.mpr
    have h := hsub.lim_le_div hbdd (by omega : m ≠ 0)
    change hsub.lim ≤ -Real.log (U f m) / (m : ℝ) at h
    rw [neg_div] at h
    linarith

/-- All finite positive-depth growth factors. -/
def growthSet (f : ℝ) : Set ℝ := {x | ∃ m : ℕ, 1 ≤ m ∧ x = growth f m}

/-- Binary interval capacity, intrinsically defined as a supremum. -/
noncomputable def capacity (f : ℝ) : ℝ := sSup (growthSet f)

theorem growthSet_nonempty (f : ℝ) : (growthSet f).Nonempty := ⟨growth f 1, 1, le_rfl, rfl⟩

theorem growthSet_bddAbove (f : ℝ) (hf : 0 ≤ f) : BddAbove (growthSet f) := by
  refine ⟨4, ?_⟩
  rintro z ⟨m, hm, rfl⟩
  exact (growth_bounds f hf m hm).2

theorem growth_le_capacity (f : ℝ) (hf : 0 ≤ f) (m : ℕ) (hm : 1 ≤ m) :
    growth f m ≤ capacity f := le_csSup (growthSet_bddAbove f hf) ⟨m, hm, rfl⟩

theorem capacity_bounds (f : ℝ) (hf : 0 ≤ f) : 2 ≤ capacity f ∧ capacity f ≤ 4 := by
  constructor
  · exact (growth_bounds f hf 1 le_rfl).1.trans (growth_le_capacity f hf 1 le_rfl)
  · apply csSup_le (growthSet_nonempty f)
    rintro z ⟨m, hm, rfl⟩
    exact (growth_bounds f hf m hm).2

/-- Finite-depth roots converge to their supremum, with no assumed Bellman
recurrence and no profile-convergence hypothesis. -/
theorem tendsto_capacity (f : ℝ) (hf : 0 ≤ f) :
    Filter.Tendsto (fun m : ℕ => U f m ^ (1 / (m : ℝ)))
      Filter.atTop (nhds (capacity f)) := by
  obtain ⟨L, _, _, ht, hmax⟩ := exists_growth_limit f hf
  have hcap : capacity f = L := by
    apply le_antisymm
    · apply csSup_le (growthSet_nonempty f)
      rintro z ⟨m, hm, rfl⟩
      exact hmax m hm
    · apply le_of_tendsto ht
      exact Filter.eventually_atTop.mpr ⟨1, fun m hm => growth_le_capacity f hf m hm⟩
  rw [hcap]
  exact ht

end NK.BinaryCapacity
