import NK.RetainedPairCertificate
import NK.RationalMomentCertificate

/-! Exact numerical certificates for pruning-tree alphabets. The tree fixes the
literal widths; dyadic reductions and numerical comparisons are all checked. -/
namespace NK.PairMomentCertificate
open RationalPowerBounds FixedPointSeries RationalMomentCertificate

def shift (D w : ℕ) : ℕ := (D / w).log2

def widthBounds (S D fn fd w : ℕ) : Bounds :=
  unitRpowBounds S D w fn fd (shift D w) 3

def WidthValid (S D fn fd w : ℕ) : Prop :=
  0 < w ∧ 0 < fd ∧ w * 2^(shift D w) ≤ D ∧ D ≤ 2*(w*2^(shift D w)) ∧
  8*(powerLogBounds S D w fn fd (shift D w)).hi ≤ S*2^3 ∧
  0 < (rpowBounds S D w fn fd (shift D w) 3).lo

instance (S D fn fd w : ℕ) : Decidable (WidthValid S D fn fd w) := by
  unfold WidthValid
  infer_instance

theorem width_lower (S D fn fd w : ℕ) (hS : 0<S) (h : WidthValid S D fn fd w) :
    ((widthBounds S D fn fd w).lo:ℝ)/S ≤ ((w:ℝ)/D)^((fn:ℝ)/fd) := by
  obtain ⟨hw,hfd,hl,hh,hr,hpos⟩ := h
  exact (unitRpowBounds_sound S D w fn fd (shift D w) 3 hS hw hfd hl hh hr hpos).1

def Valid (S D fn fd : ℕ) : PairCertificateTree → Prop
  | .leaf r => WidthValid S D fn fd r.width
  | .branch _ _ _ l r => Valid S D fn fd l ∧ Valid S D fn fd r

instance instDecidableValid (S D fn fd : ℕ) : (t : PairCertificateTree) → Decidable (Valid S D fn fd t)
  | .leaf r => inferInstanceAs (Decidable (WidthValid S D fn fd r.width))
  | .branch _ _ _ l r => by
    letI := instDecidableValid S D fn fd l
    letI := instDecidableValid S D fn fd r
    unfold Valid
    infer_instance

def lowerSum (S D fn fd : ℕ) : PairCertificateTree → ℕ
  | .leaf r => (widthBounds S D fn fd r.width).lo
  | .branch _ _ _ l r => lowerSum S D fn fd l + lowerSum S D fn fd r

theorem lowerSum_sound (S D fn fd : ℕ) (t : PairCertificateTree) (hS : 0<S)
    (h : Valid S D fn fd t) :
    ((lowerSum S D fn fd t):ℝ)/S ≤
      (t.rows.map (fun r => ((r.width:ℝ)/D)^((fn:ℝ)/fd))).sum := by
  induction t with
  | leaf r => simpa [lowerSum, PairCertificateTree.rows] using width_lower S D fn fd r.width hS h
  | branch _ _ _ l r ihl ihr =>
    simpa [lowerSum, PairCertificateTree.rows, List.map_append, List.sum_append, Nat.cast_add, add_div] using
      add_le_add (ihl h.1) (ihr h.2)

theorem moment_bound (S D fn fd B mult an ad : ℕ) (t : PairCertificateTree)
    (top : PowerData) (hS : 0<S) (h : Valid S D fn fd t)
    (htop : top.Valid S B 1 an ad)
    (hcompare : top.upper ≤ mult * lowerSum S D fn fd t) :
    (B:ℝ)^((an:ℝ)/ad) ≤ (mult:ℝ) *
      (t.rows.map (fun r => ((r.width:ℝ)/D)^((fn:ℝ)/fd))).sum := by
  have ht := (top.sound S B 1 an ad hS htop).2
  simp only [Nat.cast_one, div_one] at ht
  have hs := lowerSum_sound S D fn fd t hS h
  have hcomp : (top.upper:ℝ)/S ≤ (mult:ℝ) * ((lowerSum S D fn fd t:ℕ):ℝ)/S :=
    by rw [← Nat.cast_mul]; exact div_le_div_of_nonneg_right (by exact_mod_cast hcompare) (Nat.cast_nonneg S)
  rw [mul_div_assoc] at hcomp
  exact ht.trans (hcomp.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg mult)))

end NK.PairMomentCertificate
