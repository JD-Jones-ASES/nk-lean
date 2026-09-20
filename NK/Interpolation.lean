import NK.Definitions

/-! # Interpolation between geometric scales

The constant is retained explicitly: if a family has at least `Q^L`
elements below `B^L`, and `B^α ≤ Q`, then its interpolated all-N bound has
constant `1/Q`. This uses the integer logarithm and loses no exponent.
-/

namespace NK

/-- The arithmetic estimate behind interpolation at `L = Nat.log B N`. -/
theorem rpow_le_mul_pow_log (B Q N : ℕ) (hB : 2 ≤ B) (_hN : 1 ≤ N)
    (α : ℝ) (hα : 0 ≤ α) (hbase : (B : ℝ) ^ α ≤ (Q : ℝ)) :
    (N : ℝ) ^ α ≤ (Q : ℝ) * (Q : ℝ) ^ Nat.log B N := by
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hupper : (N : ℝ) ≤ (B : ℝ) ^ (Nat.log B N + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < B) N).le
  calc
    (N : ℝ) ^ α ≤ ((B : ℝ) ^ (Nat.log B N + 1)) ^ α :=
      Real.rpow_le_rpow (Nat.cast_nonneg N) hupper hα
    _ = ((B : ℝ) ^ α) ^ (Nat.log B N + 1) :=
      (Real.rpow_pow_comm hB0 α (Nat.log B N + 1)).symm
    _ ≤ (Q : ℝ) ^ (Nat.log B N + 1) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hB0 α) hbase _
    _ = (Q : ℝ) * (Q : ℝ) ^ Nat.log B N := by rw [pow_succ']

/-- Geometric witnesses imply an all-N estimate with the explicit constant `1/Q`.
The stage `L=0` is included, and usually is the singleton `{1}`. -/
theorem geometric_witnesses_allN (k B Q : ℕ) (hB : 2 ≤ B) (hQ : 1 ≤ Q)
    (α : ℝ) (hα : 0 ≤ α) (hbase : (B : ℝ) ^ α ≤ (Q : ℝ))
    (hstage : ∀ L : ℕ, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 (B ^ L) ∧ PowerDifferenceFree k A ∧ Q ^ L ≤ A.card)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PowerDifferenceFree k A ∧
      (1 / (Q : ℝ)) * (N : ℝ) ^ α ≤ (A.card : ℝ) := by
  obtain ⟨A, hA, hfree, hcard⟩ := hstage (Nat.log B N)
  refine ⟨A, ?_, hfree, ?_⟩
  · exact hA.trans (Finset.Icc_subset_Icc_right
      (Nat.pow_log_le_self B (by omega : N ≠ 0)))
  · have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hcardR : (Q : ℝ) ^ Nat.log B N ≤ (A.card : ℝ) := by
      exact_mod_cast hcard
    have hbound : (N : ℝ) ^ α ≤ (Q : ℝ) * (A.card : ℝ) :=
      (rpow_le_mul_pow_log B Q N hB hN α hα hbase).trans
        (mul_le_mul_of_nonneg_left hcardR hQ0.le)
    have hdiv : (N : ℝ) ^ α / Q ≤ (A.card : ℝ) :=
      (div_le_iff₀ hQ0).mpr (by simpa [mul_comm] using hbound)
    simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- The same interpolation estimate packaged as `PowerLowerBound`. -/
theorem powerLowerBound_of_geometric_witnesses (k B Q : ℕ)
    (hB : 2 ≤ B) (hQ : 1 ≤ Q) (α : ℝ) (hα : 0 ≤ α)
    (hbase : (B : ℝ) ^ α ≤ (Q : ℝ))
    (hstage : ∀ L : ℕ, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 (B ^ L) ∧ PowerDifferenceFree k A ∧ Q ^ L ≤ A.card) :
    PowerLowerBound k α := by
  refine ⟨1 / (Q : ℝ), ?_, ?_⟩
  · have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    exact one_div_pos.mpr hQ0
  · exact geometric_witnesses_allN k B Q hB hQ α hα hbase hstage

end NK
