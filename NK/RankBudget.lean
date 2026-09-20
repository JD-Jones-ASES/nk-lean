import NK.IntervalRanks
import NK.Surplus

/-! # The common rank-height budget

A strict moment surplus absorbs both the rounding height and the finite
stopping-layer loss. All heights below are actual natural-number ceilings.
-/
namespace NK

/-- Rounding reciprocal resolution to an integer costs at most a factor two. -/
theorem intervalHeight_le_two_div (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (intervalHeight ε : ℝ) ≤ 2 / ε := by
  have hone : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hhalf : (2 : ℝ)⁻¹ ≤ 1 / ε := by norm_num at *; linarith
  simpa only [intervalHeight, div_eq_mul_inv, one_mul] using Nat.ceil_le_two_mul hhalf

/-- Adding n reversed ranks of height H needs at most nH levels. -/
theorem sumRankHeight_le (n H : ℕ) (hn : 1 ≤ n) (hH : 1 ≤ H) :
    1 + n * (H - 1) ≤ n * H := by
  have hsub : H - 1 + 1 = H := Nat.sub_add_cancel hH
  nlinarith

/-- After multiplication by the cutoff, the common height has a uniform bound. -/
theorem sumRankHeight_mul_cutoff_le (n : ℕ) (σ δ : ℝ)
    (hn : 1 ≤ n) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((1 + n * (intervalHeight (σ * δ) - 1) : ℕ) : ℝ) * δ ≤ 2 * (n : ℝ) / σ := by
  have hε : 0 < σ * δ := mul_pos hσ hδ
  have hε1 : σ * δ ≤ 1 := by
    simpa using mul_le_mul hσ1 hδ1 hδ.le (show (0 : ℝ) ≤ 1 by norm_num)
  have hH : 1 ≤ intervalHeight (σ * δ) := intervalHeight_pos _ hε
  have hnat := sumRankHeight_le n (intervalHeight (σ * δ)) hn hH
  have hcast : ((1 + n * (intervalHeight (σ * δ) - 1) : ℕ) : ℝ) ≤
      (n : ℝ) * (intervalHeight (σ * δ) : ℝ) := by exact_mod_cast hnat
  have hceil := intervalHeight_le_two_div (σ * δ) hε hε1
  calc
    _ ≤ ((n : ℝ) * (intervalHeight (σ * δ) : ℝ)) * δ :=
      mul_le_mul_of_nonneg_right hcast hδ.le
    _ ≤ ((n : ℝ) * (2 / (σ * δ))) * δ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg n)) hδ.le
    _ = 2 * (n : ℝ) / σ := by field_simp

/-- The height loss factors off exactly α powers of the cutoff. -/
theorem rankBudget_factorization (h : ℕ) (δ α F P : ℝ) (hδ : 0 < δ) :
    (h : ℝ) ^ α * P * δ ^ F = ((h : ℝ) * δ) ^ α * P * δ ^ (F - α) := by
  have hsplit : δ ^ F = δ ^ α * δ ^ (F - α) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [hsplit, Real.mul_rpow (Nat.cast_nonneg h) hδ.le]
  ring

/-- Choose one stopping horizon so the combined rank height and all n stopping
pigeonhole losses fit inside a strict moment surplus. No transfer conclusion is
assumed: the result is only an explicit real inequality for the constructed height. -/
theorem exists_common_rank_budget (n : ℕ) (σ ρ α F : ℝ)
    (hn : 1 ≤ n) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 ≤ α) (hF : α < F) :
    ∃ K : ℕ, 1 ≤ K ∧
      let δ := ρ ^ K
      let H := intervalHeight (σ * δ)
      let h := 1 + n * (H - 1)
      (h : ℝ) ^ α * ((K : ℝ) + 1) ^ n * δ ^ F ≤ 1 := by
  obtain ⟨K, hK, hsmall⟩ := exists_moment_surplus_scale
    ((2 * (n : ℝ) / σ) ^ α) ρ F α n 1 hρ hρ1 hF
  refine ⟨K, hK, ?_⟩
  dsimp only
  have hδ : 0 < ρ ^ K := pow_pos hρ _
  have hδ1 : ρ ^ K ≤ 1 := pow_le_one₀ hρ.le hρ1.le
  have hheight := sumRankHeight_mul_cutoff_le n σ (ρ ^ K) hn hσ hσ1 hδ hδ1
  have hpower := Real.rpow_le_rpow
    (mul_nonneg (Nat.cast_nonneg (1 + n * (intervalHeight (σ * ρ ^ K) - 1))) hδ.le)
    hheight hα
  have hpoly : 0 ≤ ((K : ℝ) + 1) ^ n := by positivity
  have hsurplus : 0 ≤ (ρ ^ K) ^ (F - α) := Real.rpow_nonneg hδ.le _
  calc
    _ = (((1 + n * (intervalHeight (σ * ρ ^ K) - 1) : ℕ) : ℝ) * ρ ^ K) ^ α *
        ((K : ℝ) + 1) ^ n * (ρ ^ K) ^ (F - α) :=
      rankBudget_factorization _ (ρ ^ K) α F (((K : ℝ) + 1) ^ n) hδ
    _ ≤ (2 * (n : ℝ) / σ) ^ α * ((K : ℝ) + 1) ^ n * (ρ ^ K) ^ (F - α) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower hpoly) hsurplus
    _ ≤ 1 := hsmall.le

end NK
