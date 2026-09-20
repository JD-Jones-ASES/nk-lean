import NK.PerfectPowerClosure
import Mathlib

#print axioms NK.perfectPowerClosure_eq_prod
#print axioms NK.dvd_perfectPowerClosure
#print axioms NK.dvd_pow_iff_perfectPowerClosure_dvd
#print axioms NK.perfectPowerClosure_coprime_iff
#print axioms NK.perfectPowerClosure_idempotent

example : NK.perfectPowerClosure 6 9 = 729 := by
  have h := NK.perfectPowerClosure_prime_pow 6 3 2 (by decide) (by decide)
  norm_num at h
  exact h
example : NK.perfectPowerClosure 4 8 = 16 := by
  have h := NK.perfectPowerClosure_prime_pow 4 2 3 (by decide) (by decide)
  norm_num at h
  exact h
example : NK.perfectPowerClosure 2 8 = 16 := by
  have h := NK.perfectPowerClosure_prime_pow 2 2 3 (by decide) (by decide)
  norm_num at h
  exact h
example : NK.perfectPowerClosure 2 4 = 4 := by
  have h := NK.perfectPowerClosure_prime_pow 2 2 2 (by decide) (by decide)
  norm_num at h
  exact h
example : NK.perfectPowerClosure 4 (17 ^ 4) = 17 ^ 4 :=
  NK.perfectPowerClosure_pow 4 17 (by decide) (by decide)
example : NK.perfectPowerClosure 6 1 = 1 := by simp
example : NK.perfectPowerClosure 1 72 = 72 := by simp
example : 9 ∣ (0 : ℕ) ^ 6 ↔ NK.perfectPowerClosure 6 9 ∣ (0 : ℕ) ^ 6 :=
  NK.dvd_pow_iff_perfectPowerClosure_dvd 6 9 0 (by decide) (by decide)

-- Too little rounding does not preserve zero detection.
example : ¬ ((8 : ℕ) ∣ 2 ^ 2 ↔ (4 : ℕ) ∣ 2 ^ 2) := by decide
-- The naive d^k lift can be too large for nonsquarefree d.
example : ¬ ((4 : ℕ) ∣ 2 ^ 2 ↔ (16 : ℕ) ∣ 2 ^ 2) := by decide
-- The stated positive-k and positive-d domain assumptions matter.
example : ¬ ((0 : ℕ) ∣ 1 ^ 2 ↔ NK.perfectPowerClosure 2 0 ∣ 1 ^ 2) := by simp [NK.perfectPowerClosure, NK.perfectPowerRoot]
example : ¬ ((2 : ℕ) ∣ 1 ^ 0 ↔ NK.perfectPowerClosure 0 2 ∣ 1 ^ 0) := by decide
