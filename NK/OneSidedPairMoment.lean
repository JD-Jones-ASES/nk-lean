import NK.PairMomentCertificate

/-! # One-sided numeric checks for retained-pair moments

A moment lower bound uses only the lower endpoint of a reciprocal power.
Its soundness needs a positive true power and an upper enclosure of that power;
it does not need the computed lower endpoint to be positive. The lower sum is
exactly the existing `PairMomentCertificate.lowerSum`, so this checker changes
no numerical endpoint, tree data, or mathematical conclusion.
-/

namespace NK.OneSidedPairMoment

open FixedPointSeries RationalPowerBounds RationalMomentCertificate

/-- An upper bound on a positive real number gives a rounded reciprocal lower
bound. Positivity of the numerical upper endpoint follows from the hypotheses. -/
theorem reciprocal_lower (S H : ℕ) (x : ℝ) (hS : 0 < S) (hx : 0 < x)
    (hupper : x ≤ (H : ℝ) / S) :
    (((S * S / H : ℕ) : ℝ) / S) ≤ x⁻¹ := by
  have hH : 0 < H := by
    by_contra hH
    have hzero : H = 0 := Nat.eq_zero_of_not_pos hH
    rw [hzero, Nat.cast_zero, zero_div] at hupper
    exact (not_le_of_gt hx) hupper
  have hround := (FixedPointNat.enclose_ratio S H S hH hS).1
  have hinv : (S : ℝ) / H ≤ x⁻¹ := by
    simpa only [one_div, inv_div] using one_div_le_one_div_of_le hx hupper
  exact hround.trans hinv

/-- Only the reduction hypotheses actually needed for the moment lower bound. -/
def WidthValid (S D fn fd w : ℕ) : Prop :=
  0 < w ∧ 0 < fd ∧
    w * 2 ^ (PairMomentCertificate.shift D w) ≤ D ∧
    D ≤ 2 * (w * 2 ^ (PairMomentCertificate.shift D w)) ∧
    8 * (powerLogBounds S D w fn fd (PairMomentCertificate.shift D w)).hi ≤ S * 2 ^ 3

instance (S D fn fd w : ℕ) : Decidable (WidthValid S D fn fd w) := by
  unfold WidthValid
  infer_instance

/-- The old validity condition implies the cheaper condition. -/
theorem widthValid_of_full (S D fn fd w : ℕ)
    (h : PairMomentCertificate.WidthValid S D fn fd w) : WidthValid S D fn fd w :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The unchanged lower endpoint is sound without evaluating a positive lower
endpoint for the reciprocal base's power. -/
theorem width_lower (S D fn fd w : ℕ) (hS : 0 < S) (h : WidthValid S D fn fd w) :
    ((PairMomentCertificate.widthBounds S D fn fd w).lo : ℝ) / S ≤
      ((w : ℝ) / D) ^ ((fn : ℝ) / fd) := by
  obtain ⟨hw, hfd, hl, hh, hr⟩ := h
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hl
  have hx : (0 : ℝ) < (D : ℝ) / w := by positivity
  have hpower := rpowBounds_sound S D w fn fd (PairMomentCertificate.shift D w) 3
    hS hw hfd hl hh hr
  have h := reciprocal_lower S
    (rpowBounds S D w fn fd (PairMomentCertificate.shift D w) 3).hi
    (((D : ℝ) / w) ^ ((fn : ℝ) / fd)) hS (Real.rpow_pos_of_pos hx _) hpower.2
  simpa only [PairMomentCertificate.widthBounds, unitRpowBounds, reciprocal,
    ← Real.inv_rpow hx.le, inv_div] using h

/-- Check each literal width using only the one-sided reduction conditions. -/
def Valid (S D fn fd : ℕ) : PairCertificateTree → Prop
  | .leaf r => WidthValid S D fn fd r.width
  | .branch _ _ _ l r => Valid S D fn fd l ∧ Valid S D fn fd r

instance instDecidableValid (S D fn fd : ℕ) :
    (t : PairCertificateTree) → Decidable (Valid S D fn fd t)
  | .leaf r => inferInstanceAs (Decidable (WidthValid S D fn fd r.width))
  | .branch _ _ _ l r => by
    letI := instDecidableValid S D fn fd l
    letI := instDecidableValid S D fn fd r
    unfold Valid
    infer_instance

theorem valid_of_full (S D fn fd : ℕ) (t : PairCertificateTree)
    (h : PairMomentCertificate.Valid S D fn fd t) : Valid S D fn fd t := by
  induction t with
  | leaf r => exact widthValid_of_full S D fn fd r.width h
  | branch _ _ _ l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

/-- The existing exact lower sum bounds the actual moment under cheaper checks. -/
theorem lowerSum_sound (S D fn fd : ℕ) (t : PairCertificateTree) (hS : 0 < S)
    (h : Valid S D fn fd t) :
    ((PairMomentCertificate.lowerSum S D fn fd t : ℕ) : ℝ) / S ≤
      (t.rows.map (fun r => ((r.width : ℝ) / D) ^ ((fn : ℝ) / fd))).sum := by
  induction t with
  | leaf r =>
    simpa only [PairMomentCertificate.lowerSum, PairCertificateTree.rows,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      width_lower S D fn fd r.width hS h
  | branch _ _ _ l r ihl ihr =>
    simpa only [PairMomentCertificate.lowerSum, PairCertificateTree.rows,
      List.map_append, List.sum_append, Nat.cast_add, add_div] using
      add_le_add (ihl h.1) (ihr h.2)

/-- The same full moment inequality, with no computed reciprocal-lower-positivity
premise and no change to the integer lower sum or comparison. -/
theorem moment_bound (S D fn fd B mult an ad : ℕ) (t : PairCertificateTree)
    (top : PowerData) (hS : 0 < S) (h : Valid S D fn fd t)
    (htop : top.Valid S B 1 an ad)
    (hcompare : top.upper ≤ mult * PairMomentCertificate.lowerSum S D fn fd t) :
    (B : ℝ) ^ ((an : ℝ) / ad) ≤ (mult : ℝ) *
      (t.rows.map (fun r => ((r.width : ℝ) / D) ^ ((fn : ℝ) / fd))).sum := by
  have ht := (top.sound S B 1 an ad hS htop).2
  simp only [Nat.cast_one, div_one] at ht
  have hs := lowerSum_sound S D fn fd t hS h
  have hcomp : (top.upper : ℝ) / S ≤
      (mult : ℝ) * ((PairMomentCertificate.lowerSum S D fn fd t : ℕ) : ℝ) / S := by
    rw [← Nat.cast_mul]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcompare) (Nat.cast_nonneg S)
  rw [mul_div_assoc] at hcomp
  exact ht.trans (hcomp.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg mult)))

end NK.OneSidedPairMoment
