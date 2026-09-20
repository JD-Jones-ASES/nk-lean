import NK.Definitions

/-! # The full square relation at powers of two

The unit criterion is proved by explicit one-bit lifting, including the small
base case. These are arithmetic lemmas only, not a Bellman recurrence or a
certificate-transfer theorem.
-/
namespace NK.BinarySquares

/-- Reducing modulo twice a modulus exposes exactly one extra residue bit. -/
theorem mod_two_mul_cases (a M : ℕ) (hM : 0 < M) :
    a % (2 * M) = a % M ∨ a % (2 * M) = a % M + M := by
  have hlt : a % (2 * M) < 2 * M := Nat.mod_lt _ (by omega)
  have hmod : (a % (2 * M)) % M = a % M :=
    Nat.mod_mod_of_dvd a (dvd_mul_left M 2)
  by_cases h : a % (2 * M) < M
  · left
    rwa [Nat.mod_eq_of_lt h] at hmod
  · right
    have hsub : a % (2 * M) - M < M := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hsub] at hmod
    omega

/-- One of a residue and its one-bit toggle lifts any prescribed next bit. -/
theorem lift_mod_two (a u M : ℕ) (hM : 0 < M) (h : a % M = u % M) :
    a % (2 * M) = u % (2 * M) ∨ (a + M) % (2 * M) = u % (2 * M) := by
  have hr : a % M < M := Nat.mod_lt _ hM
  have hMlt : M < 2 * M := by omega
  rcases mod_two_mul_cases a M hM with ha | ha <;>
    rcases mod_two_mul_cases u M hM with hu | hu
  · left; omega
  · right
    rw [Nat.add_mod, Nat.mod_eq_of_lt hMlt, ha, hu, ← h]
    exact Nat.mod_eq_of_lt (by omega)
  · right
    rw [Nat.add_mod, Nat.mod_eq_of_lt hMlt, ha, hu, ← h]
    have heq : a % M + M + M = a % M + 2 * M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a % M < 2 * M)]
  · left; omega

/-- Adding half the old power-of-two modulus to an odd root toggles the next bit. -/
theorem odd_square_toggle (z r : ℕ) (hz : z % 2 = 1) :
    ((z + 4 * r) * (z + 4 * r)) % (16 * r) = (z * z + 8 * r) % (16 * r) := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, z = 2 * t + 1 := by
    refine ⟨z / 2, ?_⟩
    have h := Nat.mod_add_div z 2
    omega
  have hexpand : (2 * t + 1 + 4 * r) * (2 * t + 1 + 4 * r) =
      (2 * t + 1) * (2 * t + 1) + 8 * r + (16 * r) * (t + r) := by ring
  rw [hexpand, Nat.add_mul_mod_self_left]

/-- Construct an odd square root at every power of two from its residue modulo8. -/
theorem exists_odd_square_add_three (m u : ℕ) (hu : u % 8 = 1) :
    ∃ z : ℕ, z % 2 = 1 ∧ (z * z) % 2 ^ (m + 3) = u % 2 ^ (m + 3) := by
  induction m with
  | zero => exact ⟨1, by norm_num, by norm_num [hu]⟩
  | succ m ih =>
    obtain ⟨z, hz, hsq⟩ := ih
    have hM : 2 ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hN : 2 ^ (m + 1 + 3) = 2 * (8 * 2 ^ m) := by
      rw [show m + 1 + 3 = (m + 3) + 1 by omega, pow_succ, hM]
      ring
    have hMpos : 0 < 8 * 2 ^ m := by positivity
    rw [hM] at hsq
    rcases lift_mod_two (z * z) u (8 * 2 ^ m) hMpos hsq with hs | hs
    · exact ⟨z, hz, by simpa only [hN] using hs⟩
    · refine ⟨z + 4 * 2 ^ m, ?_, ?_⟩
      · simp [Nat.add_mod, Nat.mul_mod, hz]
      · rw [hN, show 2 * (8 * 2 ^ m) = 16 * 2 ^ m by ring,
          odd_square_toggle z (2 ^ m) hz]
        simpa only [show 2 * (8 * 2 ^ m) = 16 * 2 ^ m by ring] using hs

/-- Literal parity of a square, without a coprimality shortcut. -/
theorem square_mod_two (z : ℕ) : (z * z) % 2 = z % 2 := by
  have hlt : z % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mul_mod]
  interval_cases z % 2 <;> norm_num

/-- The three square residues modulo8, including the nonunit residues. -/
theorem square_mod_eight (z : ℕ) :
    (z * z) % 8 = 0 ∨ (z * z) % 8 = 1 ∨ (z * z) % 8 = 4 := by
  have hlt : z % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mul_mod]
  interval_cases z % 8 <;> norm_num

/-- An odd residue is a square modulo2^n, n≥3, precisely when it is1 modulo8. -/
theorem odd_square_iff_mod_eight (n u : ℕ) (hn : 3 ≤ n) (hu : u % 2 = 1) :
    (∃ z : ℕ, (z * z) % 2 ^ n = u % 2 ^ n) ↔ u % 8 = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    have hdiv : 8 ∣ 2 ^ n := by
      simpa using Nat.pow_dvd_pow 2 hn
    have h8 : (z * z) % 8 = u % 8 := by
      have h := congrArg (fun x : ℕ => x % 8) hz
      simpa only [Nat.mod_mod_of_dvd _ hdiv] using h
    have hu8 : (u % 8) % 2 = 1 := by
      rwa [Nat.mod_mod_of_dvd u (by norm_num : 2 ∣ 8)]
    rcases square_mod_eight z with h0 | h1 | h4
    · rw [← h8, h0] at hu8
      norm_num at hu8
    · exact h8.symm.trans h1
    · rw [← h8, h4] at hu8
      norm_num at hu8
  · intro h8
    obtain ⟨z, _, hz⟩ := exists_odd_square_add_three (n - 3) u h8
    refine ⟨z, ?_⟩
    simpa only [show n - 3 + 3 = n by omega] using hz

/-- A square congruent to zero modulo4 has an even root. -/
theorem even_root_of_square_mod_four_zero (z : ℕ) (hz : (z * z) % 4 = 0) :
    z % 2 = 0 := by
  have h := congrArg (fun x : ℕ => x % 2) hz
  simpa only [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4), square_mod_two, Nat.zero_mod] using h

/-- Dividing a square residue divisible by4 descends exactly one binary level.
Both directions are explicit root constructions; nonunit squares are included. -/
theorem square_four_mul_descent (m u : ℕ) :
    (∃ z : ℕ, (z * z) % 4 ^ (m + 1) = (4 * u) % 4 ^ (m + 1)) ↔
      ∃ y : ℕ, (y * y) % 4 ^ m = u % 4 ^ m := by
  have hpow : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [pow_succ, mul_comm]
  constructor
  · rintro ⟨z, hz⟩
    have hdiv : 4 ∣ 4 ^ (m + 1) := dvd_pow_self 4 (by omega)
    have hz4 : (z * z) % 4 = 0 := by
      have h := congrArg (fun x : ℕ => x % 4) hz
      simpa only [Nat.mod_mod_of_dvd _ hdiv, Nat.mul_mod_right] using h
    have hz2 := even_root_of_square_mod_four_zero z hz4
    obtain ⟨y, rfl⟩ : ∃ y : ℕ, z = 2 * y := by
      refine ⟨z / 2, ?_⟩
      have h := Nat.mod_add_div z 2
      omega
    refine ⟨y, ?_⟩
    rw [show (2 * y) * (2 * y) = 4 * (y * y) by ring, hpow,
      Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hz
    exact Nat.mul_left_cancel (by norm_num : 0 < 4) hz
  · rintro ⟨y, hy⟩
    refine ⟨2 * y, ?_⟩
    rw [show (2 * y) * (2 * y) = 4 * (y * y) by ring, hpow,
      Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hy]

end NK.BinarySquares
