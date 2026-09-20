import NK.PerfectPowerClosure

/-! Perfect-power closure preserves products of coprime moduli. -/
namespace NK

theorem perfectPowerClosure_mul (k d e : ℕ) (hk : 1 ≤ k)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hco : d.Coprime e) :
    perfectPowerClosure k (d*e) = perfectPowerClosure k d * perfectPowerClosure k e := by
  have hde : 1 ≤ d*e := by simpa using Nat.mul_le_mul hd he
  apply Nat.dvd_antisymm
  · change perfectPowerClosure k (d*e) ∣ perfectPowerRoot k d ^ k * perfectPowerRoot k e ^ k
    rw [← mul_pow]
    apply perfectPowerClosure_dvd_of_dvd_pow k (d*e) _ hk hde
    rw [mul_pow]
    exact Nat.mul_dvd_mul (dvd_perfectPowerClosure k d hk hd) (dvd_perfectPowerClosure k e hk he)
  · have hc := (perfectPowerClosure_coprime_iff k d e hk hd he).mpr hco
    apply hc.mul_dvd_of_dvd_of_dvd
    · exact perfectPowerClosure_dvd_of_dvd_pow k d (perfectPowerRoot k (d*e)) hk hd
        ((dvd_mul_right d e).trans (dvd_perfectPowerClosure k (d*e) hk hde))
    · exact perfectPowerClosure_dvd_of_dvd_pow k e (perfectPowerRoot k (d*e)) hk he
        ((dvd_mul_left e d).trans (dvd_perfectPowerClosure k (d*e) hk hde))

end NK
