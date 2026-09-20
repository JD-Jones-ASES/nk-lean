import NK.Certificates.BinaryApplication
import NK.Certificates.SquareChains
import NK.Certificates.Odd215Moments
import NK.Certificates.Odd437Moments

/-! The nine exact square components, assembled through the general interval
criterion. Coprimality treats the binary modulus symbolically. -/
namespace NK.Certificates

theorem square_power_bound : PowerLowerBound 2 (75806770413 / 100000000000 : ℝ) := by
  let cs : List (MomentComponent 2 (75806770413 / 100000000000 : ℝ)) :=
    [binary_component, square_chain3_component, square_chain7_component,
      square_chain11_component, square_chain31_component, square_chain59_component,
      square_chain103_component, odd215_component, odd437_component]
  apply powerLowerBound_of_intervalMoments 2 (75806770413 / 100000000000 : ℝ)
    (by decide) (by norm_num) cs
  · simp [cs]
  · change [4 ^ binaryDepth, perfectPowerClosure 2 3, perfectPowerClosure 2 7,
      perfectPowerClosure 2 11, perfectPowerClosure 2 31, perfectPowerClosure 2 59,
      perfectPowerClosure 2 103, 215^6, 437^6].Pairwise Nat.Coprime
    rw [square_chain3_closure, square_chain7_closure, square_chain11_closure,
      square_chain31_closure, square_chain59_closure, square_chain103_closure]
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb
      have hsmall : ∀ b ∈ [9, 49, 121, 961, 3481, 10609, 215^6, 437^6],
          Nat.Coprime 4 b := by decide
      have hpower (n : ℕ) : Nat.Coprime (4 ^ n) b := (hsmall b hb).pow_left n
      exact hpower binaryDepth
    · decide
  · change (75806770413 / 100000000000 : ℝ) <
      [(15494199041779 / 100000000000000 : ℝ),
        (36388946522659 / 200000000000000 : ℝ),
        (21449596099599 / 250000000000000 : ℝ),
        (53616212291671 / 500000000000000 : ℝ),
        (5572834432791 / 62500000000000 : ℝ),
        (2635800323561 / 62500000000000 : ℝ),
        (2396907967053 / 1000000000000000 : ℝ),
        (26536176765267 / 1000000000000000 : ℝ),
        (67878931321877 / 1000000000000000 : ℝ)].sum
    norm_num

end NK.Certificates
