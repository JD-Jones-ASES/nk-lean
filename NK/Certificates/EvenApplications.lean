import NK.Certificates.EvenMoments
import NK.ClosureProducts

/-! Unconditional every-N numerical applications of the full interval criterion. -/
namespace NK.Certificates

theorem k4_m5_closure : perfectPowerClosure 4 5 = 625 := by
  have h := perfectPowerClosure_prime_pow 4 5 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m5_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m5.toComponent 4 5 (4571 / 5000 : ℝ) (237478 / 1000000 : ℝ)
    (by decide) (by decide) k4_m5_valid (by norm_num) (by
      rw [k4_m5_closure]
      simpa using k4_m5_moment)

theorem k4_m13_closure : perfectPowerClosure 4 13 = 28561 := by
  have h := perfectPowerClosure_prime_pow 4 13 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m13_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m13.toComponent 4 13 (4571 / 5000 : ℝ) (207194 / 1000000 : ℝ)
    (by decide) (by decide) k4_m13_valid (by norm_num) (by
      rw [k4_m13_closure]
      simpa using k4_m13_moment)

theorem k4_m29_closure : perfectPowerClosure 4 29 = 707281 := by
  have h := perfectPowerClosure_prime_pow 4 29 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m29_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m29.toComponent 4 29 (4571 / 5000 : ℝ) (115548 / 1000000 : ℝ)
    (by decide) (by decide) k4_m29_valid (by norm_num) (by
      rw [k4_m29_closure]
      simpa using k4_m29_moment)

theorem k4_m37_closure : perfectPowerClosure 4 37 = 1874161 := by
  have h := perfectPowerClosure_prime_pow 4 37 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m37_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m37.toComponent 4 37 (4571 / 5000 : ℝ) (82357 / 1000000 : ℝ)
    (by decide) (by decide) k4_m37_valid (by norm_num) (by
      rw [k4_m37_closure]
      simpa using k4_m37_moment)

theorem k4_m51_closure : perfectPowerClosure 4 51 = 6765201 := by
  have h := perfectPowerClosure_mul 4 3 17 (by decide) (by decide) (by decide) (by decide)
  norm_num [perfectPowerClosure, perfectPowerRoot] at h
  exact h

noncomputable def k4_m51_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m51.toComponent 4 51 (4571 / 5000 : ℝ) (88517 / 1000000 : ℝ)
    (by decide) (by decide) k4_m51_valid (by norm_num) (by
      rw [k4_m51_closure]
      simpa using k4_m51_moment)

theorem k4_m53_closure : perfectPowerClosure 4 53 = 7890481 := by
  have h := perfectPowerClosure_prime_pow 4 53 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m53_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m53.toComponent 4 53 (4571 / 5000 : ℝ) (84873 / 1000000 : ℝ)
    (by decide) (by decide) k4_m53_valid (by norm_num) (by
      rw [k4_m53_closure]
      simpa using k4_m53_moment)

theorem k4_m61_closure : perfectPowerClosure 4 61 = 13845841 := by
  have h := perfectPowerClosure_prime_pow 4 61 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m61_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m61.toComponent 4 61 (4571 / 5000 : ℝ) (34356 / 1000000 : ℝ)
    (by decide) (by decide) k4_m61_valid (by norm_num) (by
      rw [k4_m61_closure]
      simpa using k4_m61_moment)

theorem k4_m16_closure : perfectPowerClosure 4 16 = 16 := by
  have h := perfectPowerClosure_prime_pow 4 2 4 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k4_m16_component : MomentComponent 4 (4571 / 5000 : ℝ) :=
  k4_m16.toComponent 4 16 (4571 / 5000 : ℝ) (64012 / 1000000 : ℝ)
    (by decide) (by decide) k4_m16_valid (by norm_num) (by
      rw [k4_m16_closure]
      simpa using k4_m16_moment)

theorem fourth_power_bound : PowerLowerBound 4 (4571 / 5000 : ℝ) := by
  let cs : List (MomentComponent 4 (4571 / 5000 : ℝ)) :=
    [k4_m5_component, k4_m13_component, k4_m29_component, k4_m37_component, k4_m51_component, k4_m53_component, k4_m61_component, k4_m16_component]
  apply powerLowerBound_of_intervalMoments 4 (4571 / 5000 : ℝ) (by decide) (by norm_num) cs
  · simp [cs]
  · change [perfectPowerClosure 4 5, perfectPowerClosure 4 13, perfectPowerClosure 4 29, perfectPowerClosure 4 37, perfectPowerClosure 4 51, perfectPowerClosure 4 53, perfectPowerClosure 4 61, perfectPowerClosure 4 16].Pairwise Nat.Coprime
    rw [k4_m5_closure, k4_m13_closure, k4_m29_closure, k4_m37_closure, k4_m51_closure, k4_m53_closure, k4_m61_closure, k4_m16_closure]
    decide
  · change (4571 / 5000 : ℝ) < [(237478 / 1000000 : ℝ), (207194 / 1000000 : ℝ), (115548 / 1000000 : ℝ), (82357 / 1000000 : ℝ), (88517 / 1000000 : ℝ), (84873 / 1000000 : ℝ), (34356 / 1000000 : ℝ), (64012 / 1000000 : ℝ)].sum
    norm_num

theorem k6_m7_closure : perfectPowerClosure 6 7 = 117649 := by
  have h := perfectPowerClosure_prime_pow 6 7 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m7_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m7.toComponent 6 7 (19059 / 20000 : ℝ) (228414690897 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m7_valid (by norm_num) (by
      rw [k6_m7_closure]
      simpa using k6_m7_moment)

theorem k6_m19_closure : perfectPowerClosure 6 19 = 47045881 := by
  have h := perfectPowerClosure_prime_pow 6 19 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m19_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m19.toComponent 6 19 (19059 / 20000 : ℝ) (25386303213 / 125000000000 : ℝ)
    (by decide) (by decide) k6_m19_valid (by norm_num) (by
      rw [k6_m19_closure]
      simpa using k6_m19_moment)

theorem k6_m31_closure : perfectPowerClosure 6 31 = 887503681 := by
  have h := perfectPowerClosure_prime_pow 6 31 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m31_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m31.toComponent 6 31 (19059 / 20000 : ℝ) (113313514093 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m31_valid (by norm_num) (by
      rw [k6_m31_closure]
      simpa using k6_m31_moment)

theorem k6_m43_closure : perfectPowerClosure 6 43 = 6321363049 := by
  have h := perfectPowerClosure_prime_pow 6 43 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m43_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m43.toComponent 6 43 (19059 / 20000 : ℝ) (132415172261 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m43_valid (by norm_num) (by
      rw [k6_m43_closure]
      simpa using k6_m43_moment)

theorem k6_m67_closure : perfectPowerClosure 6 67 = 90458382169 := by
  have h := perfectPowerClosure_prime_pow 6 67 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m67_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m67.toComponent 6 67 (19059 / 20000 : ℝ) (46780057029 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m67_valid (by norm_num) (by
      rw [k6_m67_closure]
      simpa using k6_m67_moment)

theorem k6_m79_closure : perfectPowerClosure 6 79 = 243087455521 := by
  have h := perfectPowerClosure_prime_pow 6 79 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m79_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m79.toComponent 6 79 (19059 / 20000 : ℝ) (2968686539 / 50000000000 : ℝ)
    (by decide) (by decide) k6_m79_valid (by norm_num) (by
      rw [k6_m79_closure]
      simpa using k6_m79_moment)

theorem k6_m103_closure : perfectPowerClosure 6 103 = 1194052296529 := by
  have h := perfectPowerClosure_prime_pow 6 103 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m103_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m103.toComponent 6 103 (19059 / 20000 : ℝ) (6798036087 / 200000000000 : ℝ)
    (by decide) (by decide) k6_m103_valid (by norm_num) (by
      rw [k6_m103_closure]
      simpa using k6_m103_moment)

theorem k6_m127_closure : perfectPowerClosure 6 127 = 4195872914689 := by
  have h := perfectPowerClosure_prime_pow 6 127 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m127_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m127.toComponent 6 127 (19059 / 20000 : ℝ) (11133854053 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m127_valid (by norm_num) (by
      rw [k6_m127_closure]
      simpa using k6_m127_moment)

theorem k6_m8_closure : perfectPowerClosure 6 8 = 64 := by
  have h := perfectPowerClosure_prime_pow 6 2 3 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m8_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m8.toComponent 6 8 (19059 / 20000 : ℝ) (6387145519 / 200000000000 : ℝ)
    (by decide) (by decide) k6_m8_valid (by norm_num) (by
      rw [k6_m8_closure]
      simpa using k6_m8_moment)

theorem k6_m9_closure : perfectPowerClosure 6 9 = 729 := by
  have h := perfectPowerClosure_prime_pow 6 3 2 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def k6_m9_component : MomentComponent 6 (19059 / 20000 : ℝ) :=
  k6_m9.toComponent 6 9 (19059 / 20000 : ℝ) (92503304169 / 1000000000000 : ℝ)
    (by decide) (by decide) k6_m9_valid (by norm_num) (by
      rw [k6_m9_closure]
      simpa using k6_m9_moment)

theorem sixth_power_bound : PowerLowerBound 6 (19059 / 20000 : ℝ) := by
  let cs : List (MomentComponent 6 (19059 / 20000 : ℝ)) :=
    [k6_m7_component, k6_m19_component, k6_m31_component, k6_m43_component, k6_m67_component, k6_m79_component, k6_m103_component, k6_m127_component, k6_m8_component, k6_m9_component]
  apply powerLowerBound_of_intervalMoments 6 (19059 / 20000 : ℝ) (by decide) (by norm_num) cs
  · simp [cs]
  · change [perfectPowerClosure 6 7, perfectPowerClosure 6 19, perfectPowerClosure 6 31, perfectPowerClosure 6 43, perfectPowerClosure 6 67, perfectPowerClosure 6 79, perfectPowerClosure 6 103, perfectPowerClosure 6 127, perfectPowerClosure 6 8, perfectPowerClosure 6 9].Pairwise Nat.Coprime
    rw [k6_m7_closure, k6_m19_closure, k6_m31_closure, k6_m43_closure, k6_m67_closure, k6_m79_closure, k6_m103_closure, k6_m127_closure, k6_m8_closure, k6_m9_closure]
    decide
  · change (19059 / 20000 : ℝ) < [(228414690897 / 1000000000000 : ℝ), (25386303213 / 125000000000 : ℝ), (113313514093 / 1000000000000 : ℝ), (132415172261 / 1000000000000 : ℝ), (46780057029 / 1000000000000 : ℝ), (2968686539 / 50000000000 : ℝ), (6798036087 / 200000000000 : ℝ), (11133854053 / 1000000000000 : ℝ), (6387145519 / 200000000000 : ℝ), (92503304169 / 1000000000000 : ℝ)].sum
    norm_num

end NK.Certificates
