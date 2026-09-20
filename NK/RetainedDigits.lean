import NK.IntervalRanks
import RK.LemmaA

/-! # Retaining every kth digit

The projection keeps positions `0,k,2k,...`, in low-to-high order. Every full
nonzero kth-power arc modulo a squarefree base raised to `k*e` produces a
nonzero kth-power arc at the first differing retained digit. In particular,
this applies at every prime, including primes dividing the exponent.
-/
namespace NK

/-- The retained word lists the digits at positions divisible by `k`, low first. -/
def retainedDigits (k m e x : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin e => KthPower.digit m (k * j.val) x)

@[simp] theorem retainedDigits_length (k m e x : ℕ) :
    (retainedDigits k m e x).length = e := by simp [retainedDigits]

/-- Accessing a retained coordinate recovers the corresponding original digit. -/
theorem retainedDigits_getD (k m e x j : ℕ) (hj : j < e) :
    (retainedDigits k m e x).getD j 0 = KthPower.digit m (k * j) x := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [retainedDigits]

/-- The first unequal letters form a modular kth-power arc. -/
def FirstDifferencePowerArc (k m : ℕ) (v w : List ℕ) : Prop :=
  v.length = w.length ∧ ∃ j, j < v.length ∧
    (∀ i < j, v.getD i 0 = w.getD i 0) ∧
    PowerArc k m (v.getD j 0) (w.getD j 0)

/-- An arc in the first-difference graph always has distinct endpoint words. -/
theorem FirstDifferencePowerArc.ne {k m : ℕ} {v w : List ℕ}
    (h : FirstDifferencePowerArc k m v w) : v ≠ w := by
  obtain ⟨_, j, _, _, hj⟩ := h
  intro heq
  exact hj.1 (congrArg (fun v : List ℕ => v.getD j 0) heq)

/-- The arithmetic projection theorem, stated directly in the original digits.
Only squarefreeness of the radix is needed for this forward implication. -/
theorem powerArc_retained_first_squarefree (k m e x y : ℕ)
    (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m) (he : 1 ≤ e)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e))
    (harc : PowerArc k (m ^ (k * e)) x y) :
    ∃ j, j < e ∧ (∀ i < j, KthPower.digit m (k * i) x = KthPower.digit m (k * i) y) ∧
      PowerArc k m (KthPower.digit m (k * j) x) (KthPower.digit m (k * j) y) := by
  obtain ⟨hxy, z, hcong⟩ := harc
  have hm0 : 0 < m := by omega
  have hM : 0 < m ^ (k * e) := pow_pos hm0 _
  rw [Nat.mod_eq_of_lt hy] at hcong
  have hc : z ^ k % m ^ (k * e) = KthPower.diffMod (m ^ (k * e)) x y :=
    (KthPower.diffMod_unique _ x y (z ^ k) hM hx hy hcong).symm
  have hd0 := KthPower.diffMod_ne_zero (m ^ (k * e)) x y hx hy hxy
  have hdlt := KthPower.diffMod_lt (m ^ (k * e)) x y hM
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp only [zero_pow (by omega : k ≠ 0), Nat.zero_mod] at hc
    exact hd0 hc.symm
  have hlam : z ^ k = KthPower.diffMod (m ^ (k * e)) x y +
      (z ^ k / m ^ (k * e)) * m ^ (k * e) := by
    rw [← hc]
    exact (Nat.mod_add_div' _ _).symm
  obtain ⟨r, hrlt, hrne, hrlow⟩ :=
    KthPower.exists_least_digit_ne k m e x y hm hx hy hxy
  obtain ⟨hdvd1, hdvd2⟩ :=
    KthPower.step0_exact_dvd k m e x y r hk hm he hx hy hrlt hrne hrlow
  obtain ⟨j, hj⟩ := KthPower.step2_dvd k m e _ z _ r hk hm hsf he hd0 hdlt
    hz0 hlam hrlt hdvd1 hdvd2
  subst hj
  have hjlt : j < e := by
    by_contra h
    have hcmp := Nat.mul_le_mul_left k (show e ≤ j by omega)
    omega
  obtain ⟨u, hu⟩ := KthPower.step3_pow_dvd k m e j _ z _ hk hm hsf he hd0
    hdlt hz0 hlam hjlt hdvd1 hdvd2
  have hpow := KthPower.step4_leading_power k m e j _ z _ u hk hm hsf he hd0
    hdlt hz0 hlam hjlt hdvd1 hdvd2 hu
  rw [KthPower.step1_leading_digit k m e x y (k * j) hk hm he hx hy hrlt hrlow] at hpow
  refine ⟨j, hjlt, ?_, powerArc_of_nonzeroPowerMod k m _ _
    (KthPower.digit_lt m (k * j) x hm0) (KthPower.digit_lt m (k * j) y hm0) hrne hpow⟩
  intro i hi
  exact hrlow (k * i) (Nat.mul_lt_mul_of_pos_left hi (by omega))

/-- Retaining every kth digit is a directed graph map for every squarefree radix. -/
theorem powerArc_retainedDigits_squarefree (k m e x y : ℕ)
    (hk : 1 ≤ k) (hm : 2 ≤ m) (hsf : Squarefree m) (he : 1 ≤ e)
    (hx : x < m ^ (k * e)) (hy : y < m ^ (k * e))
    (harc : PowerArc k (m ^ (k * e)) x y) :
    FirstDifferencePowerArc k m (retainedDigits k m e x) (retainedDigits k m e y) := by
  obtain ⟨j, hj, hlow, hpow⟩ :=
    powerArc_retained_first_squarefree k m e x y hk hm hsf he hx hy harc
  refine ⟨by simp, j, by simpa using hj, ?_, ?_⟩
  · intro i hi
    rw [retainedDigits_getD _ _ _ _ _ (by omega), retainedDigits_getD _ _ _ _ _ (by omega)]
    exact hlow i hi
  · simpa only [retainedDigits_getD k m e x j hj, retainedDigits_getD k m e y j hj] using hpow

/-- Prime-power specialization of the retained-digit directed projection. -/
theorem powerArc_retainedDigits (k p e x y : ℕ) (hk : 1 ≤ k) (hp : p.Prime)
    (he : 1 ≤ e) (hx : x < p ^ (k * e)) (hy : y < p ^ (k * e))
    (harc : PowerArc k (p ^ (k * e)) x y) :
    FirstDifferencePowerArc k p (retainedDigits k p e x) (retainedDigits k p e y) :=
  powerArc_retainedDigits_squarefree k p e x y hk hp.two_le
    (Irreducible.squarefree hp) he hx hy harc

/-- Endpoints of a nonzero kth-power arc have distinct retained words. -/
theorem retainedDigits_ne_of_powerArc (k p e x y : ℕ) (hk : 1 ≤ k) (hp : p.Prime)
    (he : 1 ≤ e) (hx : x < p ^ (k * e)) (hy : y < p ^ (k * e))
    (harc : PowerArc k (p ^ (k * e)) x y) :
    retainedDigits k p e x ≠ retainedDigits k p e y :=
  (powerArc_retainedDigits k p e x y hk hp he hx hy harc).ne

end NK
