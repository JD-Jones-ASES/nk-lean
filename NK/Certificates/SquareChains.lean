import NK.RationalMomentCertificate

/-! Exact P0180 square-chain components; all arithmetic is kernel checked. -/
set_option maxHeartbeats 0
set_option maxRecDepth 32768
namespace NK.Certificates
open RationalMomentCertificate

def square_chain3 : RationalAlphabetData :=
  .ofRows 2 [(0, 0, 1), (1, 1, 1)]
theorem square_chain3_valid : square_chain3.Valid 2 3 := by decide

theorem square_chain3_moment : (9:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (3:ℝ) *
    ∑ x∈square_chain3.support, ((square_chain3.width x:ℝ)/square_chain3.denominator)^(36388946522659 / 200000000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain3 1000000000000000000000000 9 3 75806770413 100000000000 36388946522659 200000000000000
    ⟨3, 4, 5289083560066002670881924, 5289083560066002670885586⟩ (fun _ => ⟨1, 1, 881513926677789627130152, 881513926677789627130218⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain3_closure : perfectPowerClosure 2 3 = 9 := by
  have h := perfectPowerClosure_prime_pow 2 3 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain3_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain3.toComponent 2 3 (75806770413 / 100000000000 : ℝ) (36388946522659 / 200000000000000 : ℝ)
    (by decide) (by decide) square_chain3_valid (by norm_num) (by
      rw [square_chain3_closure]
      simpa using square_chain3_moment)

theorem square_chain3_base : square_chain3_component.base = 9 := square_chain3_closure

def square_chain7 : RationalAlphabetData :=
  .ofRows 3 [(0, 0, 1), (1, 1, 1), (2, 2, 1)]
theorem square_chain7_valid : square_chain7.Valid 2 7 := by decide

theorem square_chain7_moment : (49:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (7:ℝ) *
    ∑ x∈square_chain7.support, ((square_chain7.width x:ℝ)/square_chain7.denominator)^(21449596099599 / 250000000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain7 1000000000000000000000000 49 7 75806770413 100000000000 21449596099599 250000000000000
    ⟨5, 5, 19110984573003323407376219, 19110984573003323407401313⟩ (fun _ => ⟨1, 0, 910046884428929932900359, 910046884428929932900399⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain7_closure : perfectPowerClosure 2 7 = 49 := by
  have h := perfectPowerClosure_prime_pow 2 7 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain7_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain7.toComponent 2 7 (75806770413 / 100000000000 : ℝ) (21449596099599 / 250000000000000 : ℝ)
    (by decide) (by decide) square_chain7_valid (by norm_num) (by
      rw [square_chain7_closure]
      simpa using square_chain7_moment)

theorem square_chain7_base : square_chain7_component.base = 49 := square_chain7_closure

def square_chain11 : RationalAlphabetData :=
  .ofRows 4 [(0, 0, 1), (1, 1, 1), (4, 2, 1), (5, 3, 1)]
theorem square_chain11_valid : square_chain11.Valid 2 11 := by decide

theorem square_chain11_moment : (121:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (11:ℝ) *
    ∑ x∈square_chain11.support, ((square_chain11.width x:ℝ)/square_chain11.denominator)^(53616212291671 / 500000000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain11 1000000000000000000000000 121 11 75806770413 100000000000 53616212291671 500000000000000
    ⟨6, 5, 37922095175877886145892334, 37922095175877886145944802⟩ (fun _ => ⟨2, 1, 861865799452010268018890, 861865799452010268018956⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain11_closure : perfectPowerClosure 2 11 = 121 := by
  have h := perfectPowerClosure_prime_pow 2 11 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain11_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain11.toComponent 2 11 (75806770413 / 100000000000 : ℝ) (53616212291671 / 500000000000000 : ℝ)
    (by decide) (by decide) square_chain11_valid (by norm_num) (by
      rw [square_chain11_closure]
      simpa using square_chain11_moment)

theorem square_chain11_base : square_chain11_component.base = 121 := square_chain11_closure

def square_chain31 : RationalAlphabetData :=
  .ofRows 7 [(0, 0, 1), (1, 1, 1), (8, 2, 1), (5, 3, 1), (2, 4, 1), (9, 5, 1), (10, 6, 1)]
theorem square_chain31_valid : square_chain31.Valid 2 31 := by decide

theorem square_chain31_moment : (961:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (31:ℝ) *
    ∑ x∈square_chain31.support, ((square_chain31.width x:ℝ)/square_chain31.denominator)^(5572834432791 / 62500000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain31 1000000000000000000000000 961 31 75806770413 100000000000 5572834432791 62500000000000
    ⟨9, 6, 182434205868434040677159672, 182434205868434040677607640⟩ (fun _ => ⟨2, 1, 840710626122143370758222, 840710626122143370758290⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain31_closure : perfectPowerClosure 2 31 = 961 := by
  have h := perfectPowerClosure_prime_pow 2 31 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain31_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain31.toComponent 2 31 (75806770413 / 100000000000 : ℝ) (5572834432791 / 62500000000000 : ℝ)
    (by decide) (by decide) square_chain31_valid (by norm_num) (by
      rw [square_chain31_closure]
      simpa using square_chain31_moment)

theorem square_chain31_base : square_chain31_component.base = 961 := square_chain31_closure

def square_chain59 : RationalAlphabetData :=
  .ofRows 9 [(0, 0, 1), (1, 1, 1), (28, 2, 1), (17, 3, 1), (22, 4, 1), (4, 5, 1), (26, 6, 1), (20, 7, 1), (29, 8, 1)]
theorem square_chain59_valid : square_chain59.Valid 2 59 := by decide

theorem square_chain59_moment : (3481:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (59:ℝ) *
    ∑ x∈square_chain59.support, ((square_chain59.width x:ℝ)/square_chain59.denominator)^(2635800323561 / 62500000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain59 1000000000000000000000000 3481 59 75806770413 100000000000 2635800323561 62500000000000
    ⟨11, 6, 484006771446852536554726159, 484006771446852536555960325⟩ (fun _ => ⟨3, 0, 911500511199746893895760, 911500511199746893895799⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain59_closure : perfectPowerClosure 2 59 = 3481 := by
  have h := perfectPowerClosure_prime_pow 2 59 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain59_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain59.toComponent 2 59 (75806770413 / 100000000000 : ℝ) (2635800323561 / 62500000000000 : ℝ)
    (by decide) (by decide) square_chain59_valid (by norm_num) (by
      rw [square_chain59_closure]
      simpa using square_chain59_moment)

theorem square_chain59_base : square_chain59_component.base = 3481 := square_chain59_closure

def square_chain103 : RationalAlphabetData :=
  .ofRows 11 [(0, 0, 1), (1, 1, 1), (29, 2, 1), (92, 3, 1), (2, 4, 1), (61, 5, 1), (17, 6, 1), (30, 7, 1), (93, 8, 1), (18, 9, 1), (19, 10, 1)]
theorem square_chain103_valid : square_chain103.Valid 2 103 := by decide

theorem square_chain103_moment : (10609:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (103:ℝ) *
    ∑ x∈square_chain103.support, ((square_chain103.width x:ℝ)/square_chain103.denominator)^(2396907967053 / 1000000000000000 : ℝ) := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using (moment_bound square_chain103 1000000000000000000000000 10609 103 75806770413 100000000000 2396907967053 1000000000000000
    ⟨13, 6, 1126506721701019780921914765, 1126506721701019780924997168⟩ (fun _ => ⟨3, 0, 994268951192905840671062, 994268951192905840671094⟩)
    (by decide) (by decide) (by decide) (by decide))

theorem square_chain103_closure : perfectPowerClosure 2 103 = 10609 := by
  have h := perfectPowerClosure_prime_pow 2 103 1 (by decide) (by decide)
  norm_num at h
  exact h

noncomputable def square_chain103_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) :=
  square_chain103.toComponent 2 103 (75806770413 / 100000000000 : ℝ) (2396907967053 / 1000000000000000 : ℝ)
    (by decide) (by decide) square_chain103_valid (by norm_num) (by
      rw [square_chain103_closure]
      simpa using square_chain103_moment)

theorem square_chain103_base : square_chain103_component.base = 10609 := square_chain103_closure

end NK.Certificates
