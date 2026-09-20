import Mathlib

/-! # Nonsingular kth-power units modulo prime powers

A concrete square-zero Newton step lifts a kth-power root through each prime
power. The final statement quantifies over ordinary natural-number residues.
-/
namespace NK

/-- One Newton correction is exact when the current error has square zero. -/
theorem exists_pow_eq_of_sq_error_zero {R : Type*} [CommRing R]
    (k : ℕ) (a u : R) (herr : (a ^ k - u) ^ 2 = 0)
    (hder : IsUnit ((k : R) * a ^ (k - 1))) : ∃ z : R, z ^ k = u := by
  obtain ⟨d, hd⟩ := hder.exists_right_inv
  let v := -(a ^ k - u) * d
  have hv : v ^ 2 = 0 := by simp [v, mul_pow, herr]
  have ht := Polynomial.eval_add_of_sq_eq_zero (Polynomial.X ^ k : Polynomial R) a v hv
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at ht
  refine ⟨a + v, ?_⟩
  rw [ht]
  calc
    a ^ k + (k : R) * a ^ (k - 1) * v =
        a ^ k - (a ^ k - u) * ((k : R) * a ^ (k - 1) * d) := by dsimp [v]; ring
    _ = u := by rw [hd]; ring

/-- A unit root modulo `p^n` lifts by one level whenever `p` does not divide `k`. -/
theorem exists_pow_mod_prime_succ (p k u n a : ℕ) (hp : p.Prime)
    (hk : ¬ p ∣ k) (hu : ¬ p ∣ u) (hn : 1 ≤ n)
    (ha : a ^ k % p ^ n = u % p ^ n) :
    ∃ z : ℕ, z ^ k % p ^ (n + 1) = u % p ^ (n + 1) := by
  let R := ZMod (p ^ (n + 1))
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hk0 : k ≠ 0 := by intro h; apply hk; simp [h]
  have hpn : p ∣ p ^ n := dvd_pow_self _ (by omega)
  have hpa : ¬ p ∣ a := by
    intro h
    apply hu
    exact (Nat.ModEq.dvd_iff ha hpn).mp (dvd_pow h hk0)
  have hkunit : IsUnit (k : R) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < n + 1)).mpr hk
  have haunit : IsUnit (a : R) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < n + 1)).mpr hpa
  have hder : IsUnit ((k : R) * (a : R) ^ (k - 1)) := hkunit.mul (haunit.pow _)
  have hdiv : (p : ℤ) ^ n ∣ (a : ℤ) ^ k - u := by
    simpa only [Nat.cast_pow] using (Nat.ModEq.dvd (show Nat.ModEq (p ^ n) u (a ^ k) from ha.symm))
  obtain ⟨t, ht⟩ := hdiv
  have herror : (a : R) ^ k - (u : R) = (p : R) ^ n * (t : R) := by
    have ht' := congrArg (Int.castRingHom R) ht
    simpa only [map_sub, map_pow, map_mul, map_natCast, Int.coe_castRingHom] using ht'
  have hzero : (p : R) ^ (n * 2) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by omega)
  have herr : ((a : R) ^ k - (u : R)) ^ 2 = 0 := by
    rw [herror, mul_pow, ← pow_mul, hzero, zero_mul]
  obtain ⟨z, hz⟩ := exists_pow_eq_of_sq_error_zero k (a : R) (u : R) herr hder
  refine ⟨z.val, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ (p ^ (n + 1))).mp
  simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hz

/-- For a prime not dividing the exponent, a unit is a kth power modulo any
positive prime power exactly when it is a kth power modulo the prime. -/
theorem exists_pow_mod_prime_power_iff (p k u n : ℕ) (hp : p.Prime)
    (hk : ¬ p ∣ k) (hu : ¬ p ∣ u) (hn : 1 ≤ n) :
    (∃ z : ℕ, z ^ k % p ^ n = u % p ^ n) ↔
      ∃ z : ℕ, z ^ k % p = u % p := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Nat.ModEq.of_dvd (dvd_pow_self _ (by omega)) hz⟩
  · intro h
    induction n, hn using Nat.le_induction with
    | base => simpa using h
    | succ n hn ih =>
      obtain ⟨a, ha⟩ := ih
      exact exists_pow_mod_prime_succ p k u n a hp hk hu hn ha

/-- The square-unit specialization at any odd prime. -/
theorem exists_sq_mod_prime_power_iff (p u n : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hu : ¬ p ∣ u) (hn : 1 ≤ n) :
    (∃ z : ℕ, z ^ 2 % p ^ n = u % p ^ n) ↔
      ∃ z : ℕ, z ^ 2 % p = u % p := by
  apply exists_pow_mod_prime_power_iff p 2 u n hp ?_ hu hn
  intro h
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)

end NK
