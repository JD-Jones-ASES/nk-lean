import Mathlib

/-! # Power-difference-free sets and ordered interval alphabets

Definitions in this module have their ordinary mathematical meanings. None
asserts a lower bound or assumes the transfer theorem being developed.
-/
namespace NK

/-- A finite set has no nonzero positive k-th-power difference. -/
def PowerDifferenceFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ z : ℕ, 0 < z → a + z ^ k ∉ A

/-- A uniform all-N lower bound for sets avoiding k-th-power differences. -/
def PowerLowerBound (k : ℕ) (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ PowerDifferenceFree k A ∧
      c * (N : ℝ) ^ α ≤ (A.card : ℝ)

/-- A positive-width interval contained in the unit interval. -/
structure UnitInterval where
  left : ℝ
  width : ℝ
  left_nonneg : 0 ≤ left
  width_pos : 0 < width
  right_le_one : left + width ≤ 1

/-- The full modular power relation, using all residues including nonunits. -/
def PowerArc (k m x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ z : ℕ, (x + z ^ k) % m = y % m

/-- An interval alphabet orders every nontrivial modular k-th-power arc. -/
structure IntervalAlphabet (k m : ℕ) where
  support : Finset ℕ
  residue_lt : ∀ x ∈ support, x < m
  interval : (x : ℕ) → x ∈ support → UnitInterval
  ordered : ∀ x (hx : x ∈ support) y (hy : y ∈ support), PowerArc k m x y →
    (interval x hx).left + (interval x hx).width ≤ (interval y hy).left

/-- Its f-moment is the sum of the positive interval widths to real power f. -/
noncomputable def IntervalAlphabet.moment {k m : ℕ} (A : IntervalAlphabet k m) (f : ℝ) : ℝ :=
  ∑ x ∈ A.support.attach, (A.interval x.1 x.2).width ^ f

end NK
