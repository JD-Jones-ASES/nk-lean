import NK.IntervalTransfer
import NK.ClosureLift

/-! A closed end-to-end application through closure, moments and the full
transfer theorem. This familiar square-root bound is a boundary control,
not one of the new numerical headline applications. -/
namespace TransferControl
open NK

noncomputable def lower : UnitInterval := ⟨0, 1/2, by norm_num, by norm_num, by norm_num⟩
noncomputable def upper : UnitInterval := ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num⟩

noncomputable def seed : IntervalAlphabet 2 3 where
  support := {0,1}
  residue_lt x hx := by simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega
  interval x _ := if x=0 then lower else upper
  ordered x hx y hy harc := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (harc.1 rfl)
    · norm_num [lower, upper]
    · obtain ⟨_, z, hz⟩ := harc
      have hrem : z % 3 < 3 := Nat.mod_lt z (by decide)
      rw [Nat.add_mod, Nat.pow_mod] at hz
      interval_cases hr : z % 3 <;> norm_num [hr] at hz
    · exact False.elim (harc.1 rfl)

lemma seed_moment : seed.moment 1 = 1 := by
  classical
  have hw : ∀ x (hx : x ∈ seed.support), (seed.interval x hx).width = (1/2 : ℝ) := by
    intro x hx
    change (if x=0 then lower else upper).width = 1/2
    split_ifs <;> rfl
  unfold IntervalAlphabet.moment
  simp only [hw, Real.rpow_one]
  norm_num [seed]

lemma closure_eq : perfectPowerClosure 2 3 = 9 := by
  have h := perfectPowerClosure_prime_pow 2 3 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def component : MomentComponent 2 (1/2) where
  base := perfectPowerClosure 2 3
  root := perfectPowerRoot 2 3
  base_ge_two := by rw [closure_eq]; decide
  base_eq_power := rfl
  alphabet := seed.closureLift (by decide) (by decide)
  f := 1
  f_nonneg := by norm_num
  width_lt_one x hx := by
    change (if x % 3 = 0 then lower else upper).width < 1
    split_ifs <;> norm_num [lower, upper]
  moment_bound := by
    rw [seed.closureLift_moment, seed_moment, closure_eq]
    norm_num [← Real.sqrt_eq_rpow]

/-- A genuine unconditional all-N consequence exercises the complete pipeline. -/
theorem square_root_bound : PowerLowerBound 2 (1/2) := by
  apply powerLowerBound_of_intervalMoments 2 (1/2) (by decide) (by norm_num) [component]
    (by simp) (by simp)
  norm_num [component]

#print axioms square_root_bound
end TransferControl
