import NK.Certificates.Odd437Geometry
import NK.Certificates.Odd437Numeric

namespace NK.Certificates

noncomputable def odd437Low : RetainedPairAlphabet 2 19 23 3 :=
  odd437Tree.toAlphabet 2 19 23 3 100000118525840 (by decide +kernel) odd437_tree_valid odd437_tree_geometry

noncomputable def odd437_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) where
  base := 6964478817623209
  root := 83453453
  base_ge_two := by decide
  base_eq_power := by decide
  alphabet := odd437Low.toIntervalAlphabet (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  f := (67878931321877 / 1000000000000000 : ℝ)
  f_nonneg := by norm_num
  width_lt_one x hx := by
    exact odd437Tree.toAlphabet_width_lt_one 2 19 23 3 100000118525840 (by decide +kernel)
      odd437_tree_valid odd437_tree_geometry _ (Finset.mem_filter.mp hx).2
  moment_bound := by
    rw [RetainedPairAlphabet.toIntervalAlphabet_moment]
    rw [odd437Low, PairCertificateTree.toAlphabet_moment _ _ _ _ _ _ _ _ _ odd437Key odd437_tree_sorted]
    simpa using odd437_moment

end NK.Certificates
