import NK.Certificates.BinaryMoments
import NK.Certificates.BinaryDepth
import NK.IntervalTransfer

/-! # The certified binary component for the improved square exponent

The depth is finite but enormous. Its base and square root are kept as
symbolic natural powers; no numeral expansion is used in the proof.
-/

namespace NK.Certificates

open NK.BinaryPolicy

theorem binary_alphabet_exists :
    ∃ A : IntervalAlphabet 2 (4 ^ 1000000000000000),
      (∀ x (hx : x ∈ A.support), (A.interval x hx).width < 1) ∧
      (((4 ^ 1000000000000000 : ℕ) : ℝ) ^ (75806770413 / 100000000000 : ℝ)) ≤
        A.moment (15494199041779 / 100000000000000 : ℝ) := by
  obtain ⟨A, hwidth, hmoment⟩ := binaryPolicy.exists_half_depth
    (15494199041779 / 100000000000000 : ℝ)
    (1430119207986461 / 500000000000000 : ℝ) binaryWeights
    (by norm_num [Set.mem_Icc]) (by norm_num) binaryWeights_bounds
    (fun i => binaryRows_growth i) 1000000000000000 (by decide) 1
  have hroot : binaryWeights 1 = 1 := by norm_num [binaryWeights]
  rw [hroot, mul_one] at hmoment
  exact ⟨A, hwidth, binary_depth_moment.trans hmoment⟩

noncomputable def binary_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) where
  base := 4 ^ 1000000000000000
  root := 2 ^ 1000000000000000
  base_ge_two := le_trans (by decide : 2 ≤ (4 : ℕ))
    (le_self_pow (by decide : 1 ≤ (4 : ℕ)) (by decide : (1000000000000000 : ℕ) ≠ 0))
  base_eq_power := by
    have h (n : ℕ) : (4 : ℕ) ^ n = ((2 : ℕ) ^ n) ^ 2 := pow_right_comm 2 2 n
    exact h 1000000000000000
  alphabet := Classical.choose binary_alphabet_exists
  f := (15494199041779 / 100000000000000 : ℝ)
  f_nonneg := by norm_num
  width_lt_one := (Classical.choose_spec binary_alphabet_exists).1
  moment_bound := (Classical.choose_spec binary_alphabet_exists).2

theorem binary_component_base : binary_component.base = 4 ^ 1000000000000000 := rfl

theorem binary_component_root : binary_component.root = 2 ^ 1000000000000000 := rfl

theorem binary_component_f : binary_component.f = (15494199041779 / 100000000000000 : ℝ) := rfl

end NK.Certificates
