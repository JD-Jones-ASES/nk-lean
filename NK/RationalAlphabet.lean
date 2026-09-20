import NK.ClosureLift
import NK.IntervalTransfer

/-! Finite integer certificates for literal modular interval geometry. The
checker ranges over all residue roots, including nonunits. -/
namespace NK

structure RationalAlphabetData where
  support : Finset ℕ
  start : ℕ → ℕ
  width : ℕ → ℕ
  denominator : ℕ

namespace RationalAlphabetData

/-- A finite table of (residue,start,width) with a common denominator.
Repeated residues, if present, use the first row; all counts use the actual support. -/
def ofRows (D : ℕ) (rows : List (ℕ × ℕ × ℕ)) : RationalAlphabetData where
  support := (rows.map Prod.fst).toFinset
  start x := ((rows.find? (fun row => row.1 == x)).map (fun row => row.2.1)).getD 0
  width x := ((rows.find? (fun row => row.1 == x)).map (fun row => row.2.2)).getD 0
  denominator := D

/-- Every quantified check is finite and uses only natural arithmetic. -/
def Valid (d : RationalAlphabetData) (k m : ℕ) : Prop :=
  0 < d.denominator ∧
  (∀ x ∈ d.support, x < m ∧ 0 < d.width x ∧ d.width x < d.denominator ∧
    d.start x + d.width x ≤ d.denominator) ∧
  ∀ x ∈ d.support, ∀ y ∈ d.support, ∀ z ∈ Finset.range m,
    x ≠ y → (x + z ^ k) % m = y → d.start x + d.width x ≤ d.start y

instance (d : RationalAlphabetData) (k m : ℕ) : Decidable (d.Valid k m) := by
  unfold Valid
  infer_instance

/-- Successful finite checks construct an actual real interval alphabet. -/
noncomputable def toAlphabet (d : RationalAlphabetData) (k m : ℕ) (hv : d.Valid k m) :
    IntervalAlphabet k m where
  support := d.support
  residue_lt x hx := (hv.2.1 x hx).1
  interval x hx := {
    left := (d.start x : ℝ) / d.denominator
    width := (d.width x : ℝ) / d.denominator
    left_nonneg := by positivity
    width_pos := div_pos (by exact_mod_cast (hv.2.1 x hx).2.1) (by exact_mod_cast hv.1)
    right_le_one := by
      rw [← add_div]
      apply (div_le_one (by exact_mod_cast hv.1 : (0:ℝ)<d.denominator)).mpr
      exact_mod_cast (hv.2.1 x hx).2.2.2 }
  ordered x hx y hy harc := by
    obtain ⟨hne,z,hz⟩ := harc
    have hm : 0 < m := by have := (hv.2.1 x hx).1; omega
    have hzy : (x + (z % m) ^ k) % m = y := by
      simpa only [Nat.add_mod, Nat.pow_mod, Nat.mod_mod,
        Nat.mod_eq_of_lt (hv.2.1 y hy).1] using hz
    have h := hv.2.2 x hx y hy (z%m) (Finset.mem_range.mpr (Nat.mod_lt z hm)) hne hzy
    change (d.start x : ℝ)/d.denominator + (d.width x : ℝ)/d.denominator ≤
      (d.start y : ℝ)/d.denominator
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast h

@[simp] theorem toAlphabet_width (d : RationalAlphabetData) (k m : ℕ) (hv : d.Valid k m)
    (x : ℕ) (hx : x ∈ (d.toAlphabet k m hv).support) :
    ((d.toAlphabet k m hv).interval x hx).width = (d.width x : ℝ)/d.denominator := rfl

theorem toAlphabet_width_lt_one (d : RationalAlphabetData) (k m : ℕ) (hv : d.Valid k m)
    (x : ℕ) (hx : x ∈ (d.toAlphabet k m hv).support) :
    ((d.toAlphabet k m hv).interval x hx).width < 1 := by
  rw [toAlphabet_width]
  apply (div_lt_one (by exact_mod_cast hv.1 : (0:ℝ)<d.denominator)).mpr
  exact_mod_cast (hv.2.1 x hx).2.2.1

/-- The finite numerical sum is exactly the constructed real moment. -/
theorem toAlphabet_moment (d : RationalAlphabetData) (k m : ℕ) (hv : d.Valid k m) (f : ℝ) :
    (d.toAlphabet k m hv).moment f = ∑ x ∈ d.support, ((d.width x : ℝ)/d.denominator)^f := by
  classical
  simp only [IntervalAlphabet.moment, toAlphabet_width]
  exact Finset.sum_attach d.support (fun x => ((d.width x : ℝ)/d.denominator)^f)

/-- Literal seed geometry and its numerical inequality give a full moment
component after canonical closure. This lemma does not assume a transfer bound. -/
noncomputable def toComponent (d : RationalAlphabetData) (k m : ℕ) (α f : ℝ)
    (hk : 1 ≤ k) (hm : 2 ≤ m) (hv : d.Valid k m) (hf : 0 ≤ f)
    (hZ : (perfectPowerClosure k m : ℝ)^α ≤
      ((perfectPowerClosure k m / m : ℕ) : ℝ) *
        ∑ x ∈ d.support, ((d.width x : ℝ)/d.denominator)^f) : MomentComponent k α where
  base := perfectPowerClosure k m
  root := perfectPowerRoot k m
  base_ge_two := hm.trans (le_perfectPowerClosure k m hk (by omega))
  base_eq_power := rfl
  alphabet := (d.toAlphabet k m hv).closureLift hk (by omega)
  f := f
  f_nonneg := hf
  width_lt_one x hx := d.toAlphabet_width_lt_one k m hv (x%m) (by
    exact (Finset.mem_filter.mp hx).2)
  moment_bound := by
    rw [IntervalAlphabet.closureLift_moment, toAlphabet_moment]
    exact hZ

end RationalAlphabetData
end NK
