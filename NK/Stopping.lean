import NK.Definitions

/-! # An abstract stopping-mass pigeonhole lemma

If mass grows by a factor `q` except for the mass stopped at each layer,
then some layer carries a definite fraction of the normalized initial mass.
This result uses only a recurrence and its two endpoint values.
-/
namespace NK

/-- Some stopping layer has normalized mass at least `1 / (K + 1)`.
The proof does not assume any interval, graph, or lower-bound conclusion. -/
theorem stopping_mass
    (K : ℕ) (q : ℝ) (A T : ℕ → ℝ)
    (hK : 1 ≤ K) (hq : 1 ≤ q)
    (_hA : ∀ j, 0 ≤ A j) (_hT : ∀ j, 0 ≤ T j)
    (hA0 : A 0 = 1) (hAK : A K = 0)
    (hrec : ∀ j, j < K → q * A j ≤ A (j + 1) + T j) :
    ∃ j, j < K ∧ q ^ (j + 1) ≤ ((K : ℝ) + 1) * T j := by
  by_contra hnone
  have hsmall : ∀ j, j < K → ((K : ℝ) + 1) * T j < q ^ (j + 1) := by
    intro j hj
    exact lt_of_not_ge (fun h => hnone ⟨j, hj, h⟩)
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hK0 : 0 ≤ (K : ℝ) + 1 := by positivity
  have hbound : ∀ j, j ≤ K →
      (((K : ℝ) + 1) - (j : ℝ)) * q ^ j ≤ ((K : ℝ) + 1) * A j := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [hA0]
    | succ j ih =>
      intro hj
      have hjlt : j < K := Nat.lt_of_succ_le hj
      have hjle : j ≤ K := le_of_lt hjlt
      have hgrowth := mul_le_mul_of_nonneg_left (hrec j hjlt) hK0
      have hprevious := mul_le_mul_of_nonneg_left (ih hjle) hq0
      have hstop := hsmall j hjlt
      rw [pow_succ] at hstop ⊢
      push_cast
      nlinarith
  have hfinal := hbound K (le_refl K)
  rw [hAK] at hfinal
  have hpow : 0 < q ^ K := pow_pos (by linarith) K
  nlinarith

end NK
