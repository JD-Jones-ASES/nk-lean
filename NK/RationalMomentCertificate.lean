import NK.RationalAlphabet
import NK.RationalPowerBounds

/-! Numerical certificates use only natural inequalities. The checker soundness
connects the outward-rounded endpoints to actual real powers and moments. -/
namespace NK
namespace RationalMomentCertificate

open FixedPointSeries RationalPowerBounds

/-- A supplied reduction and a claimed enclosing pair, at the ambient scale. -/
structure PowerData where
  shift : ℕ
  depth : ℕ
  lower : ℕ
  upper : ℕ

/-- Checks for a rational base at least one. -/
def PowerData.Valid (c : PowerData) (S a b fn fd : ℕ) : Prop :=
  0 < b ∧ 0 < fd ∧ b * 2^c.shift ≤ a ∧ a ≤ 2*(b*2^c.shift) ∧
  8*(powerLogBounds S a b fn fd c.shift).hi ≤ S*2^c.depth ∧
  c.lower ≤ (rpowBounds S a b fn fd c.shift c.depth).lo ∧
  (rpowBounds S a b fn fd c.shift c.depth).hi ≤ c.upper

instance (c : PowerData) (S a b fn fd : ℕ) : Decidable (c.Valid S a b fn fd) := by
  unfold PowerData.Valid
  infer_instance

/-- Checks for the reciprocal rational base, a unit width. -/
def PowerData.UnitValid (c : PowerData) (S a b fn fd : ℕ) : Prop :=
  0 < b ∧ 0 < fd ∧ b * 2^c.shift ≤ a ∧ a ≤ 2*(b*2^c.shift) ∧
  8*(powerLogBounds S a b fn fd c.shift).hi ≤ S*2^c.depth ∧
  0 < (rpowBounds S a b fn fd c.shift c.depth).lo ∧
  c.lower ≤ (unitRpowBounds S a b fn fd c.shift c.depth).lo ∧
  (unitRpowBounds S a b fn fd c.shift c.depth).hi ≤ c.upper

instance (c : PowerData) (S a b fn fd : ℕ) : Decidable (c.UnitValid S a b fn fd) := by
  unfold PowerData.UnitValid
  infer_instance

theorem PowerData.sound (c : PowerData) (S a b fn fd : ℕ) (hS : 0<S)
    (h : c.Valid S a b fn fd) :
    (c.lower:ℝ)/S ≤ ((a:ℝ)/b)^((fn:ℝ)/fd) ∧
    ((a:ℝ)/b)^((fn:ℝ)/fd) ≤ (c.upper:ℝ)/S := by
  obtain ⟨hb,hfd,hl,hh,hr,hlo,hhi⟩ := h
  have he := rpowBounds_sound S a b fn fd c.shift c.depth hS hb hfd hl hh hr
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (Nat.cast_nonneg S)).trans he.1
  · exact he.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (Nat.cast_nonneg S))

theorem PowerData.unit_sound (c : PowerData) (S a b fn fd : ℕ) (hS : 0<S)
    (h : c.UnitValid S a b fn fd) :
    (c.lower:ℝ)/S ≤ ((b:ℝ)/a)^((fn:ℝ)/fd) ∧
    ((b:ℝ)/a)^((fn:ℝ)/fd) ≤ (c.upper:ℝ)/S := by
  obtain ⟨hb,hfd,hl,hh,hr,hpos,hlo,hhi⟩ := h
  have he := unitRpowBounds_sound S a b fn fd c.shift c.depth hS hb hfd hl hh hr hpos
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (Nat.cast_nonneg S)).trans he.1
  · exact he.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (Nat.cast_nonneg S))

/-- A finite sum of certified lower endpoints bounds the literal moment. -/
theorem sum_lower (d : RationalAlphabetData) (S fn fd : ℕ) (c : ℕ → PowerData)
    (hS : 0<S) (hc : ∀ x∈d.support, (c x).UnitValid S d.denominator (d.width x) fn fd) :
    ((∑ x ∈ d.support, (c x).lower : ℕ):ℝ)/S ≤
      ∑ x ∈ d.support, ((d.width x:ℝ)/d.denominator)^((fn:ℝ)/fd) := by
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun x hx => ((c x).unit_sound S _ _ fn fd hS (hc x hx)).1)

/-- Successful finite certificates imply the actual closure moment inequality. -/
theorem moment_bound (d : RationalAlphabetData) (S B mult an ad fn fd : ℕ)
    (top : PowerData) (c : ℕ → PowerData) (hS : 0<S)
    (htop : top.Valid S B 1 an ad)
    (hc : ∀ x∈d.support, (c x).UnitValid S d.denominator (d.width x) fn fd)
    (hcompare : top.upper ≤ mult * ∑ x∈d.support, (c x).lower) :
    (B:ℝ)^((an:ℝ)/ad) ≤ (mult:ℝ) *
      ∑ x∈d.support, ((d.width x:ℝ)/d.denominator)^((fn:ℝ)/fd) := by
  have ht := (top.sound S B 1 an ad hS htop).2
  simp only [Nat.cast_one, div_one] at ht
  have hs := sum_lower d S fn fd c hS hc
  have hcomp : (top.upper:ℝ)/S ≤
      (mult:ℝ) * (((∑ x∈d.support, (c x).lower:ℕ):ℝ)/S) := by
    rw [← mul_div_assoc, ← Nat.cast_mul]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcompare) (Nat.cast_nonneg S)
  exact ht.trans (hcomp.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg mult)))

end RationalMomentCertificate
end NK
