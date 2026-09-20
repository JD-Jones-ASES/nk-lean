import NK.Certificates.Odd215Geometry
import NK.Certificates.Odd215Numeric

namespace NK.Certificates

noncomputable def odd215Low : RetainedPairAlphabet 2 5 43 3 :=
  odd215Tree.toAlphabet 2 5 43 3 99999974386028 (by decide +kernel) odd215_tree_valid odd215_tree_geometry

noncomputable def odd215_component : MomentComponent 2 (75806770413 / 100000000000 : ℝ) where
  base := 98771297640625
  root := 9938375
  base_ge_two := by decide
  base_eq_power := by decide
  alphabet := odd215Low.toIntervalAlphabet (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  f := (26536176765267 / 1000000000000000 : ℝ)
  f_nonneg := by norm_num
  width_lt_one x hx := by
    exact odd215Tree.toAlphabet_width_lt_one 2 5 43 3 99999974386028 (by decide +kernel)
      odd215_tree_valid odd215_tree_geometry _ (Finset.mem_filter.mp hx).2
  moment_bound := by
    rw [RetainedPairAlphabet.toIntervalAlphabet_moment]
    rw [odd215Low, PairCertificateTree.toAlphabet_moment _ _ _ _ _ _ _ _ _ odd215Key odd215_tree_sorted]
    simpa using odd215_moment

end NK.Certificates
