import NK.FixedPointSeries
import NK.NumericReduction

/-! # Computable rational-power enclosures

All endpoints are natural numbers at a supplied positive scale. Reduction
shifts are certificate inputs and their domain conditions are explicit
theorem hypotheses. Multiplication, repeated squaring, and inversion are
rounded outwards. No search procedure or native evaluation is trusted.
-/

namespace NK.RationalPowerBounds

open NK.FixedPointNat NK.FixedPointSeries

/-- Enclose log(a/b) using a supplied nonnegative dyadic shift. -/
def logPosBounds (S a b s : ℕ) : Bounds :=
  add (scaleRatio (logBounds S 2 1) s 1) (logBounds S a (b * 2 ^ s))

theorem logPosBounds_sound (S a b s : ℕ) (hS : 0 < S) (hb : 0 < b)
    (hlo : b * 2 ^ s ≤ a) (hhi : a ≤ 2 * (b * 2 ^ s)) :
    Encloses S (logPosBounds S a b s) (Real.log ((a : ℝ) / b)) := by
  have hp : (0 : ℝ) < 2 ^ s := by positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hlo
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have h2 := logBounds_sound S 2 1 hS (by decide) (by decide) (by decide)
  have hs := scaleRatio_sound S (logBounds S 2 1) _ s 1 hS (by decide) h2
  have hu := logBounds_sound S a (b * 2 ^ s) hS (by positivity) hlo hhi
  have h := add_sound S _ _ _ _ hs hu
  have hid : Real.log ((a : ℝ) / b) =
      Real.log 2 * s + Real.log ((a : ℝ) / ((b * 2 ^ s : ℕ) : ℝ)) := by
    have heq : (a : ℝ) / b = (2 : ℝ) ^ s * ((a : ℝ) / ((b * 2 ^ s : ℕ) : ℝ)) := by
      push_cast
      field_simp
    rw [heq, Real.log_mul hp.ne' (by positivity), Real.log_pow]
    ring
  rw [hid]
  simpa [logPosBounds] using h

def square (S : ℕ) (v : Bounds) : Bounds :=
  ⟨v.lo * v.lo / S, ceilDiv (v.hi * v.hi) S⟩

theorem square_sound (S : ℕ) (v : Bounds) (x : ℝ) (hS : 0 < S)
    (hv : Encloses S v x) : Encloses S (square S v) (x ^ 2) := by
  simpa [square, Encloses, pow_two] using
    enclose_mul S v.lo v.hi v.lo v.hi x x hS hv hv

def squarings (S : ℕ) (v : Bounds) : ℕ → Bounds
  | 0 => v
  | n + 1 => square S (squarings S v n)

theorem squarings_sound (S : ℕ) (v : Bounds) (x : ℝ) (n : ℕ)
    (hS : 0 < S) (hv : Encloses S v x) :
    Encloses S (squarings S v n) (x ^ (2 ^ n)) := by
  induction n with
  | zero => simpa [squarings] using hv
  | succ n ih =>
    simpa [squarings, Nat.pow_succ, pow_mul] using square_sound S _ _ hS ih

/-- Range-reduced exponential followed by outward-rounded squarings. -/
def expPosBounds (S a b m : ℕ) : Bounds :=
  squarings S (expBounds S a (b * 2 ^ m)) m

theorem expPosBounds_sound (S a b m : ℕ) (hS : 0 < S) (hb : 0 < b)
    (hred : 8 * a ≤ b * 2 ^ m) :
    Encloses S (expPosBounds S a b m) (Real.exp ((a : ℝ) / b)) := by
  have h := squarings_sound S (expBounds S a (b * 2 ^ m)) _ m hS
    (expBounds_sound S a (b * 2 ^ m) hS (by positivity) hred)
  rw [← NK.NumericReduction.exp_dyadic] at h
  have heq : (2 : ℝ) ^ m * ((a : ℝ) / ((b * 2 ^ m : ℕ) : ℝ)) = (a : ℝ) / b := by
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- Evaluate the two endpoints with the same verified reduction depth. -/
def expInterval (S : ℕ) (v : Bounds) (m : ℕ) : Bounds :=
  ⟨(expPosBounds S v.lo S m).lo, (expPosBounds S v.hi S m).hi⟩

theorem encloses_order (S : ℕ) (v : Bounds) (x : ℝ) (hS : 0 < S)
    (hv : Encloses S v x) : v.lo ≤ v.hi := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  exact_mod_cast (div_le_div_iff_of_pos_right hsR).mp (hv.1.trans hv.2)

theorem expInterval_sound (S : ℕ) (v : Bounds) (x : ℝ) (m : ℕ)
    (hS : 0 < S) (hv : Encloses S v x) (hred : 8 * v.hi ≤ S * 2 ^ m) :
    Encloses S (expInterval S v m) (Real.exp x) := by
  have horder := encloses_order S v x hS hv
  have hl := expPosBounds_sound S v.lo S m hS hS
    ((Nat.mul_le_mul_left 8 horder).trans hred)
  have hh := expPosBounds_sound S v.hi S m hS hS hred
  simp only [Encloses, expInterval]
  exact ⟨hl.1.trans (Real.exp_le_exp.mpr hv.1),
    (Real.exp_le_exp.mpr hv.2).trans hh.2⟩

def powerLogBounds (S a b fn fd s : ℕ) : Bounds :=
  scaleRatio (logPosBounds S a b s) fn fd

/-- Nonnegative rational powers of rational bases at least one. -/
def rpowBounds (S a b fn fd s m : ℕ) : Bounds :=
  expInterval S (powerLogBounds S a b fn fd s) m

theorem rpowBounds_sound (S a b fn fd s m : ℕ)
    (hS : 0 < S) (hb : 0 < b) (hfd : 0 < fd)
    (hlo : b * 2 ^ s ≤ a) (hhi : a ≤ 2 * (b * 2 ^ s))
    (hred : 8 * (powerLogBounds S a b fn fd s).hi ≤ S * 2 ^ m) :
    Encloses S (rpowBounds S a b fn fd s m)
      (((a : ℝ) / b) ^ ((fn : ℝ) / fd)) := by
  have hl := logPosBounds_sound S a b s hS hb hlo hhi
  have hf := scaleRatio_sound S (logPosBounds S a b s) _ fn fd hS hfd hl
  have h := expInterval_sound S (powerLogBounds S a b fn fd s) _ m hS hf hred
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hlo
  have hx : (0 : ℝ) < (a : ℝ) / b := by positivity
  simpa [rpowBounds, Real.rpow_def_of_pos hx] using h

/-- Invert a positive enclosure, swapping endpoints and rounding outwards. -/
def reciprocal (S : ℕ) (v : Bounds) : Bounds :=
  ⟨S * S / v.hi, ceilDiv (S * S) v.lo⟩

theorem reciprocal_sound (S : ℕ) (v : Bounds) (x : ℝ) (hS : 0 < S)
    (hv : Encloses S v x) (hlo : 0 < v.lo) :
    Encloses S (reciprocal S v) x⁻¹ := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  have hhi : 0 < v.hi := hlo.trans_le (encloses_order S v x hS hv)
  have hloR : (0 : ℝ) < (v.lo : ℝ) / S := by positivity
  have hx : 0 < x := hloR.trans_le hv.1
  have hl := (enclose_ratio S v.hi S hhi hS).1
  have hh := (enclose_ratio S v.lo S hlo hS).2
  have hiInv := one_div_le_one_div_of_le hx hv.2
  have loInv := one_div_le_one_div_of_le hloR hv.1
  simp only [one_div, inv_div] at hiInv loInv
  exact ⟨hl.trans hiInv, loInv.trans hh⟩

/-- Powers of unit widths are reciprocals of the corresponding powers
of their reciprocal bases. -/
def unitRpowBounds (S a b fn fd s m : ℕ) : Bounds :=
  reciprocal S (rpowBounds S a b fn fd s m)

theorem unitRpowBounds_sound (S a b fn fd s m : ℕ)
    (hS : 0 < S) (hb : 0 < b) (hfd : 0 < fd)
    (hlo : b * 2 ^ s ≤ a) (hhi : a ≤ 2 * (b * 2 ^ s))
    (hred : 8 * (powerLogBounds S a b fn fd s).hi ≤ S * 2 ^ m)
    (hpos : 0 < (rpowBounds S a b fn fd s m).lo) :
    Encloses S (unitRpowBounds S a b fn fd s m)
      (((b : ℝ) / a) ^ ((fn : ℝ) / fd)) := by
  have h := reciprocal_sound S _ _ hS
    (rpowBounds_sound S a b fn fd s m hS hb hfd hlo hhi hred) hpos
  have hx : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  simpa [unitRpowBounds, ← Real.inv_rpow hx, inv_div] using h

end NK.RationalPowerBounds
