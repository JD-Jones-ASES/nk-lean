import NK.FixedPointNat
import NK.NumericBounds

/-! # Computable outward-rounded positive series

The functions in this file use natural arithmetic. A state carries the
current term and accumulated sum, so powers are updated by recurrence.
Every rounding operation is included in the soundness theorems. The
logarithm wrapper uses the larger remainder proved in `NumericBounds`.
-/

namespace NK.FixedPointSeries

open NK.FixedPointNat NK.NumericBounds

structure Bounds where
  lo : ℕ
  hi : ℕ
deriving DecidableEq, Repr

def Encloses (S : ℕ) (v : Bounds) (x : ℝ) : Prop :=
  (v.lo : ℝ) / S ≤ x ∧ x ≤ (v.hi : ℝ) / S

def zero : Bounds := ⟨0, 0⟩
def one (S : ℕ) : Bounds := ⟨S, S⟩
def add (v w : Bounds) : Bounds := ⟨v.lo + w.lo, v.hi + w.hi⟩
def scaleRatio (v : Bounds) (a b : ℕ) : Bounds :=
  ⟨v.lo * a / b, ceilDiv (v.hi * a) b⟩
def ratio (S a b : ℕ) : Bounds := ⟨a * S / b, ceilDiv (a * S) b⟩

theorem zero_sound (S : ℕ) : Encloses S zero 0 := by
  simp [Encloses, zero]

theorem one_sound (S : ℕ) (hS : 0 < S) : Encloses S (one S) 1 := by
  have h : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  simp [Encloses, one, h]

theorem add_sound (S : ℕ) (v w : Bounds) (x y : ℝ)
    (hv : Encloses S v x) (hw : Encloses S w y) :
    Encloses S (add v w) (x + y) := by
  dsimp [Encloses, add] at *
  push_cast
  simpa only [add_div] using And.intro (add_le_add hv.1 hw.1) (add_le_add hv.2 hw.2)

theorem ratio_sound (S a b : ℕ) (hS : 0 < S) (hb : 0 < b) :
    Encloses S (ratio S a b) ((a : ℝ) / b) :=
  enclose_ratio a b S hb hS

theorem scaleRatio_sound (S : ℕ) (v : Bounds) (x : ℝ) (a b : ℕ)
    (hS : 0 < S) (hb : 0 < b) (hv : Encloses S v x) :
    Encloses S (scaleRatio v a b) (x * ((a : ℝ) / b)) := by
  have hsR : (0 : ℝ) ≤ S := by positivity
  have ha : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hlo := div_le_div_of_nonneg_right (floor_ratio_le (v.lo * a) b hb) hsR
  have hhi := div_le_div_of_nonneg_right (ratio_le_ceil (v.hi * a) b hb) hsR
  dsimp [Encloses, scaleRatio]
  constructor
  · apply hlo.trans
    simpa only [Nat.cast_mul, div_div, mul_div_assoc, div_mul_eq_mul_div, mul_comm (b : ℝ) (S : ℝ)] using
      mul_le_mul_of_nonneg_right hv.1 ha
  · apply le_trans _ hhi
    simpa only [Nat.cast_mul, div_div, mul_div_assoc, div_mul_eq_mul_div, mul_comm (b : ℝ) (S : ℝ)] using
      mul_le_mul_of_nonneg_right hv.2 ha

structure SeriesState where
  term : Bounds
  total : Bounds
deriving DecidableEq, Repr

/-- At state n, `term` encloses x^n/n! and `total` encloses its first n terms. -/
def taylorState (S a b : ℕ) : ℕ → SeriesState
  | 0 => ⟨one S, zero⟩
  | n + 1 =>
    let v := taylorState S a b n
    ⟨scaleRatio v.term a (b * (n + 1)), add v.total v.term⟩

def taylor (S a b n : ℕ) : Bounds := (taylorState S a b n).total

theorem taylorState_sound (S a b : ℕ) (hS : 0 < S) (hb : 0 < b) (n : ℕ) :
    Encloses S (taylorState S a b n).term (((a : ℝ) / b) ^ n / n.factorial) ∧
    Encloses S (taylorState S a b n).total (expTaylor ((a : ℝ) / b) n) := by
  induction n with
  | zero =>
    simpa [taylorState, expTaylor] using And.intro (one_sound S hS) (zero_sound S)
  | succ n ih =>
    constructor
    · have h := scaleRatio_sound S (taylorState S a b n).term _ a (b * (n + 1))
        hS (by positivity) ih.1
      change Encloses S (scaleRatio (taylorState S a b n).term a (b * (n + 1))) _
      convert h using 1
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      field_simp
    · have h := add_sound S (taylorState S a b n).total (taylorState S a b n).term
        _ _ ih.2 ih.1
      simpa [taylorState, expTaylor, Finset.sum_range_succ] using h

theorem taylor_sound (S a b n : ℕ) (hS : 0 < S) (hb : 0 < b) :
    Encloses S (taylor S a b n) (expTaylor ((a : ℝ) / b) n) :=
  (taylorState_sound S a b hS hb n).2

/-- The odd power advances by multiplication by z²; the sum stores
the first n odd powers divided by their odd indices. -/
def oddState (S a b : ℕ) : ℕ → SeriesState
  | 0 => ⟨ratio S a b, zero⟩
  | n + 1 =>
    let v := oddState S a b n
    ⟨scaleRatio v.term (a * a) (b * b),
      add v.total (scaleRatio v.term 1 (2 * n + 1))⟩

def atanhSum (S a b n : ℕ) : Bounds :=
  scaleRatio (oddState S a b n).total 2 1

theorem oddState_sound (S a b : ℕ) (hS : 0 < S) (hb : 0 < b) (n : ℕ) :
    Encloses S (oddState S a b n).term (((a : ℝ) / b) ^ (2 * n + 1)) ∧
    Encloses S (oddState S a b n).total
      (∑ j ∈ Finset.range n, ((a : ℝ) / b) ^ (2 * j + 1) / (2 * j + 1)) := by
  induction n with
  | zero =>
    simpa [oddState] using And.intro (ratio_sound S a b hS hb) (zero_sound S)
  | succ n ih =>
    constructor
    · have h := scaleRatio_sound S (oddState S a b n).term _ (a * a) (b * b)
        hS (by positivity) ih.1
      change Encloses S (scaleRatio (oddState S a b n).term (a * a) (b * b)) _
      convert h using 1
      have he : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [he, pow_add]
      push_cast
      ring
    · have ht := scaleRatio_sound S (oddState S a b n).term _ 1 (2 * n + 1)
        hS (by omega) ih.1
      have h := add_sound S (oddState S a b n).total
        (scaleRatio (oddState S a b n).term 1 (2 * n + 1)) _ _ ih.2 ht
      simpa [oddState, Finset.sum_range_succ, div_eq_mul_inv] using h

theorem atanhSum_sound (S a b n : ℕ) (hS : 0 < S) (hb : 0 < b) :
    Encloses S (atanhSum S a b n) (atanhLogSum ((a : ℝ) / b) n) := by
  have h := scaleRatio_sound S (oddState S a b n).total _ 2 1 hS (by decide)
    (oddState_sound S a b hS hb n).2
  simpa [atanhSum, atanhLogSum, mul_comm] using h

/-- Round a known positive remainder upwards, retaining the lower endpoint. -/
def upperPad (v : Bounds) (S a b : ℕ) : Bounds :=
  ⟨v.lo, v.hi + ceilDiv (a * S) b⟩

theorem upperPad_sound (S : ℕ) (v : Bounds) (a b : ℕ) (x y : ℝ)
    (hS : 0 < S) (hb : 0 < b) (hv : Encloses S v y)
    (hlo : y ≤ x) (hhi : x ≤ y + (a : ℝ) / b) :
    Encloses S (upperPad v S a b) x := by
  have ht := (enclose_ratio a b S hb hS).2
  refine ⟨hv.1.trans hlo, hhi.trans ?_⟩
  simpa [upperPad, Nat.cast_add, add_div] using add_le_add hv.2 ht

/-- Thirty-one Taylor terms and a rounded analytic tail of 10^(-60). -/
def expBounds (S a b : ℕ) : Bounds :=
  upperPad (taylor S a b 31) S 1 (10 ^ 60)

theorem expBounds_sound (S a b : ℕ) (hS : 0 < S) (hb : 0 < b)
    (hab : 8 * a ≤ b) :
    Encloses S (expBounds S a b) (Real.exp ((a : ℝ) / b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hx : (a : ℝ) / b ≤ 1 / 8 := by
    apply (div_le_iff₀ hbR).mpr
    have h : (8 : ℝ) * a ≤ b := by exact_mod_cast hab
    linarith
  have he := expTaylor_eighth_bounds_thirtyone ((a : ℝ) / b) (by positivity) hx
  apply upperPad_sound S _ 1 (10 ^ 60) _ _ hS (by positivity)
    (taylor_sound S a b 31 hS hb) he.1
  simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using he.2

/-- Forty odd terms and a rounded analytic tail of 10^(-38), for a/b in [1,2]. -/
def logBounds (S a b : ℕ) : Bounds :=
  upperPad (atanhSum S (a - b) (a + b) 40) S 1 (10 ^ 38)

theorem logBounds_sound (S a b : ℕ) (hS : 0 < S) (hb : 0 < b)
    (hba : b ≤ a) (hab : a ≤ 2 * b) :
    Encloses S (logBounds S a b) (Real.log ((a : ℝ) / b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbaR : (b : ℝ) ≤ a := by exact_mod_cast hba
  have habR : (a : ℝ) ≤ 2 * b := by exact_mod_cast hab
  have hx1 : (1 : ℝ) ≤ (a : ℝ) / b := (le_div_iff₀ hbR).mpr (by simpa using hbaR)
  have hx2 : (a : ℝ) / b ≤ 2 := (div_le_iff₀ hbR).mpr habR
  have he := log_unit_bounds_forty ((a : ℝ) / b) hx1 hx2
  have hz : (((a : ℝ) / b) - 1) / (((a : ℝ) / b) + 1) =
      ((a - b : ℕ) : ℝ) / ((a + b : ℕ) : ℝ) := by
    rw [Nat.cast_sub hba, Nat.cast_add]
    field_simp
  rw [hz] at he
  apply upperPad_sound S _ 1 (10 ^ 38) _ _ hS (by positivity)
    (atanhSum_sound S (a - b) (a + b) 40 hS (by omega)) he.1
  simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using he.2

end NK.FixedPointSeries
