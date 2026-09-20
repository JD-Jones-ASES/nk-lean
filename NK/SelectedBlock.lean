import NK.WordIntervals

/-! # A concrete ranked block selected from an interval alphabet

The stopping tree produces an actual finite set of equal-length words. Encoding
those words preserves cardinality and interval width, so common-scale rounding
produces a ranked block. No selected-block conclusion is assumed as an input.
-/
namespace NK
namespace IntervalAlphabet

variable {k b : ℕ}

/-- The interval-alphabet moment is the one-letter moment of its finite subtype. -/
theorem moment_eq_alphabetMoment (A : IntervalAlphabet k b) (f : ℝ) :
    A.moment f = StoppingWords.alphabetMoment
      (fun a : A.Letter => (A.letterInterval a).width) f := by
  classical
  simp only [moment, StoppingWords.alphabetMoment, letterInterval,
    Finset.univ_eq_attach]

/-- A stopping layer of concrete words gives a nonempty ranked block, with one
common interval-height cost and the cardinality supplied by its actual moment. -/
theorem exists_selected_rankedBlock (A : IntervalAlphabet k b) (n K : ℕ)
    (f α σ ρ : ℝ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k)
    (hK : 1 ≤ K) (hf : 0 ≤ f) (hα : 0 ≤ α) (hσ : 0 < σ)
    (hσw : ∀ x (hx : x ∈ A.support), σ ≤ (A.interval x hx).width)
    (hwρ : ∀ x (hx : x ∈ A.support), (A.interval x hx).width ≤ ρ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hZ : (b : ℝ) ^ α ≤ A.moment f) :
    ∃ e : ℕ, 1 ≤ e ∧ e ≤ K ∧ ∃ C : Finset ℕ, ∃ h : ℕ → ℕ,
      KthPower.RankedBlock k (b ^ e) C h (intervalHeight (σ * ρ ^ K)) ∧
      C.Nonempty ∧
      ((b ^ e : ℕ) : ℝ) ^ α ≤ ((K : ℝ) + 1) * (C.card : ℝ) * (ρ ^ K) ^ f := by
  classical
  let w : A.Letter → ℝ := fun a => (A.letterInterval a).width
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hσletter : ∀ a, σ ≤ w a := fun a => hσw a.val a.property
  have hρletter : ∀ a, w a ≤ ρ := fun a => hwρ a.val a.property
  have hmoment : (b : ℝ) ^ α ≤ StoppingWords.alphabetMoment w f := by
    simpa only [w, ← A.moment_eq_alphabetMoment f] using hZ
  obtain ⟨e, he1, heK, E, _hEdef, hwords, hmass⟩ :=
    StoppingWords.exists_terminal_layer w K f ρ σ (b : ℝ) α hK hσ hσletter
      hρletter hρ0.le hρ1 hf hb1 hα hmoment
  have hlen : ∀ v ∈ E, v.length = e := fun v hv => (hwords v hv).1
  have hminimum : ∀ v ∈ E, σ * ρ ^ K ≤ StoppingWords.width w v :=
    fun v hv => (hwords v hv).2.1.le
  have hE : E.Nonempty := by
    by_contra hn
    have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hpositive : 0 < (b : ℝ) ^ ((e : ℝ) * α) :=
      Real.rpow_pos_of_pos hb0 _
    simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul] at hmass
    exact (not_le_of_gt hpositive) hmass
  let B := A.wordAlphabet n e hk hb hbase he1 E hlen
  have hcard : B.support.card = E.card :=
    A.wordAlphabet_card n e hk hb hbase he1 E hlen
  have hB : B.support.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact Finset.card_pos.mpr hE
  have hε : 0 < σ * ρ ^ K := mul_pos hσ (pow_pos hρ0 K)
  have hwidth : ∀ x (hx : x ∈ B.support), σ * ρ ^ K ≤ (B.interval x hx).width :=
    A.wordAlphabet_min_width n e hk hb hbase he1 E hlen (σ * ρ ^ K) hminimum
  refine ⟨e, he1, heK, B.support, intervalRank B (σ * ρ ^ K),
    B.rankedBlock (σ * ρ ^ K) hε hwidth, hB, ?_⟩
  rw [hcard, Nat.cast_pow, ← Real.rpow_natCast_mul hb0.le e α]
  exact hmass

end IntervalAlphabet
end NK
