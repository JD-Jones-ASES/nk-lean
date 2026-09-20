import Mathlib.Data.Nat.Factorization.Root

/-! # The canonical perfect-power closure of an arbitrary modulus

The root is the product of `p^ceil(v_p(d)/k)` over the prime factors of d.
Its kth power is the least positive perfect kth-power multiple of d.

Mathlib already supplies this root as `Nat.ceilRoot` and proves its
divisibility adjunction using factorization. We identify the transparent
prime-product definition with that existing function, then derive the
closure properties needed by the interval lift. The arithmetic adjunction
is a Mathlib result; its application to arbitrary-modulus interval
alphabets is part of the present development.

The definitions are total, but their intended domain here is `k ≥ 1`,
`d ≥ 1`. The zero-detection theorem allows every z, including zero.
-/

namespace NK

/-- Round every prime valuation of d up after division by k. -/
def perfectPowerRoot (k d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, p ^ ((d.factorization p + k - 1) / k)

/-- The least positive perfect kth-power integer divisible by d, for k,d≥1. -/
def perfectPowerClosure (k d : ℕ) : ℕ := perfectPowerRoot k d ^ k

/-- The explicit prime product is Mathlib's ceiling root on the intended domain. -/
theorem perfectPowerRoot_eq_ceilRoot (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    perfectPowerRoot k d = Nat.ceilRoot k d := by
  have hk0 : k ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  rw [Nat.ceilRoot, if_neg (by simp [hk0, hd0])]
  rfl

/-- The closure also has the customary product formula with rounded exponents. -/
theorem perfectPowerClosure_eq_prod (k d : ℕ) :
    perfectPowerClosure k d =
      ∏ p ∈ d.primeFactors, p ^ (k * ((d.factorization p + k - 1) / k)) := by
  unfold perfectPowerClosure perfectPowerRoot
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_mul, Nat.mul_comm]

/-- On a prime-power modulus the rounded exponent is completely explicit. -/
theorem perfectPowerClosure_prime_pow (k p e : ℕ) (hp : p.Prime) (he : e ≠ 0) :
    perfectPowerClosure k (p ^ e) = p ^ (k * ((e + k - 1) / k)) := by
  rw [perfectPowerClosure_eq_prod, Nat.primeFactors_prime_pow he hp]
  simp [hp.factorization_pow]

/-- The closure is literally a kth power; the displayed root is a witness. -/
theorem perfectPowerClosure_isPower (k d : ℕ) :
    ∃ r : ℕ, perfectPowerClosure k d = r ^ k :=
  ⟨perfectPowerRoot k d, rfl⟩

/-- The rounded root is positive on the intended domain. -/
theorem perfectPowerRoot_pos (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    0 < perfectPowerRoot k d := by
  rw [perfectPowerRoot_eq_ceilRoot k d hk hd]
  exact Nat.pos_of_ne_zero (Nat.ceilRoot_ne_zero.mpr ⟨by omega, by omega⟩)

/-- In particular the closure is a positive modulus. -/
theorem perfectPowerClosure_pos (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    0 < perfectPowerClosure k d :=
  pow_pos (perfectPowerRoot_pos k d hk hd) k

/-- Every original modulus divides its canonical perfect-power closure. -/
theorem dvd_perfectPowerClosure (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    d ∣ perfectPowerClosure k d := by
  rw [perfectPowerClosure, perfectPowerRoot_eq_ceilRoot k d hk hd]
  exact Nat.dvd_ceilRoot_pow (by omega)

/-- Divisibility by d of a kth power is detected by the rounded root. -/
theorem dvd_pow_iff_perfectPowerRoot_dvd (k d z : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d) :
    d ∣ z ^ k ↔ perfectPowerRoot k d ∣ z := by
  rw [perfectPowerRoot_eq_ceilRoot k d hk hd]
  exact Nat.dvd_pow_iff_ceilRoot_dvd (by omega)

/-- Zero detection: d and its closure divide exactly the same kth powers.
No nonzero hypothesis on z is needed. -/
theorem dvd_pow_iff_perfectPowerClosure_dvd (k d z : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d) :
    d ∣ z ^ k ↔ perfectPowerClosure k d ∣ z ^ k := by
  rw [perfectPowerClosure, Nat.pow_dvd_pow_iff (by omega : k ≠ 0)]
  exact dvd_pow_iff_perfectPowerRoot_dvd k d z hk hd

/-- The closure divides every perfect kth-power multiple of d. -/
theorem perfectPowerClosure_dvd_of_dvd_pow (k d z : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d) (hz : d ∣ z ^ k) :
    perfectPowerClosure k d ∣ z ^ k :=
  (dvd_pow_iff_perfectPowerClosure_dvd k d z hk hd).mp hz

/-- Consequently it is the least positive perfect kth-power multiple of d. -/
theorem perfectPowerClosure_le_of_dvd_pow (k d z : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d) (hz : 1 ≤ z) (hdiv : d ∣ z ^ k) :
    perfectPowerClosure k d ≤ z ^ k :=
  Nat.le_of_dvd (pow_pos (by omega : 0 < z) k)
    (perfectPowerClosure_dvd_of_dvd_pow k d z hk hd hdiv)

/-- The closure is at least the original positive modulus. -/
theorem le_perfectPowerClosure (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    d ≤ perfectPowerClosure k d :=
  Nat.le_of_dvd (perfectPowerClosure_pos k d hk hd) (dvd_perfectPowerClosure k d hk hd)

/-- The closure divides the elementary (usually larger) perfect-power lift d^k. -/
theorem perfectPowerClosure_dvd_pow_self (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    perfectPowerClosure k d ∣ d ^ k :=
  perfectPowerClosure_dvd_of_dvd_pow k d d hk hd (dvd_pow_self d (by omega))

/-- Canonical closure preserves and reflects coprimality, as required by CRT. -/
theorem perfectPowerClosure_coprime_iff (k d e : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d) (he : 1 ≤ e) :
    Nat.Coprime (perfectPowerClosure k d) (perfectPowerClosure k e) ↔ Nat.Coprime d e := by
  constructor
  · intro h
    exact (h.coprime_dvd_left (dvd_perfectPowerClosure k d hk hd)).coprime_dvd_right
      (dvd_perfectPowerClosure k e hk he)
  · intro h
    exact ((h.pow k k).coprime_dvd_left
      (perfectPowerClosure_dvd_pow_self k d hk hd)).coprime_dvd_right
      (perfectPowerClosure_dvd_pow_self k e hk he)

/-- An already perfect kth-power modulus is unchanged by closure. -/
theorem perfectPowerClosure_pow (k z : ℕ) (hk : 1 ≤ k) (hz : 1 ≤ z) :
    perfectPowerClosure k (z ^ k) = z ^ k := by
  rw [perfectPowerClosure, perfectPowerRoot_eq_ceilRoot k (z ^ k) hk
    (Nat.one_le_pow k z hz), Nat.ceilRoot_pow_self (by omega : k ≠ 0)]

/-- Taking closure twice does not enlarge the modulus again. -/
theorem perfectPowerClosure_idempotent (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    perfectPowerClosure k (perfectPowerClosure k d) = perfectPowerClosure k d := by
  exact perfectPowerClosure_pow k (perfectPowerRoot k d) hk
    (perfectPowerRoot_pos k d hk hd)

/-- The harmless unit modulus is included in the theorem domain. -/
@[simp] theorem perfectPowerClosure_one (k : ℕ) : perfectPowerClosure k 1 = 1 := by
  simp [perfectPowerClosure, perfectPowerRoot]

/-- At k=1 no rounding occurs. -/
@[simp] theorem perfectPowerClosure_one_left (d : ℕ) (hd : 1 ≤ d) :
    perfectPowerClosure 1 d = d := by
  rw [perfectPowerClosure, perfectPowerRoot_eq_ceilRoot 1 d (by decide) hd]
  simp

end NK
