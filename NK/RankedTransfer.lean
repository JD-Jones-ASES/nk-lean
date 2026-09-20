import NK.Interpolation
import RK.LemmaB

/-! # All-N transfer from a ranked block

This module reuses the perfect-power-base word construction in the
MIT-licensed `JD-Jones-ASES/rk-lean`, pinned by the project manifest.
Its rank decreases along arcs. No squarefree assumption on the root of
the perfect-power base occurs in this theorem.
-/

namespace NK

/-- A singleton avoids positive k-th-power differences, for every natural k. -/
theorem singleton_powerDifferenceFree (k a : ℕ) :
    PowerDifferenceFree k ({a} : Finset ℕ) := by
  intro x hx z hz hmem
  have hxa : x = a := Finset.mem_singleton.mp hx
  have hza : x + z ^ k = a := Finset.mem_singleton.mp hmem
  have hpos : 0 < z ^ k := pow_pos hz k
  omega

/-- A ranked support on an arbitrary perfect k-th-power modulus supplies
geometric witnesses at every length, including length zero. -/
theorem rankedBlock_geometric_witnesses (k n P : ℕ) (hk : 1 ≤ k)
    (hP : P = n ^ k) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : KthPower.RankedBlock k P C h H) (hH : 1 ≤ H) (L : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 ((P * H) ^ L) ∧
      PowerDifferenceFree k A ∧ C.card ^ L ≤ A.card := by
  by_cases hL : L = 0
  · subst L
    refine ⟨{1}, ?_, singleton_powerDifferenceFree k 1, ?_⟩ <;> simp
  · have hL1 : 1 ≤ L := by omega
    refine ⟨KthPower.integerSet P L H C h,
      KthPower.integerSet_subset k P L H C h hC hH, ?_, ?_⟩
    · exact KthPower.lemmaB_pdf k n P hk hP C h H hC L hL1
    · exact (KthPower.integerSet_card k P L H C h hC hH).ge

/-- The full exponent, with an all-N constant, from a ranked block on a
perfect k-th-power modulus. The resulting constant is `1 / C.card`. -/
theorem powerLowerBound_of_rankedBlock (k n P : ℕ) (hk : 1 ≤ k)
    (hP : P = n ^ k) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : KthPower.RankedBlock k P C h H) (hH : 1 ≤ H)
    (hPH : 2 ≤ P * H) (hcard : 1 ≤ C.card) (α : ℝ) (hα : 0 ≤ α)
    (hbase : ((P * H : ℕ) : ℝ) ^ α ≤ (C.card : ℝ)) :
    PowerLowerBound k α :=
  powerLowerBound_of_geometric_witnesses k (P * H) C.card hPH hcard α hα hbase
    (rankedBlock_geometric_witnesses k n P hk hP C h H hC hH)

end NK
