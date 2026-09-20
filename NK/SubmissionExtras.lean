import NK.ClosureLift

/-! A construction-free public statement of the canonical copying theorem. -/
namespace NK

/-- Copy every occupied seed residue to its entire canonical closure fiber. -/
theorem closure_interval_lift (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (A : IntervalAlphabet k d) :
    ∃ B : IntervalAlphabet k (perfectPowerClosure k d),
      B.support = (Finset.range (perfectPowerClosure k d)).filter (fun x => x % d ∈ A.support) ∧
      B.support.card = (perfectPowerClosure k d / d) * A.support.card ∧
      ∀ f : ℝ, B.moment f = (perfectPowerClosure k d / d : ℕ) * A.moment f := by
  exact ⟨A.closureLift hk hd, rfl, A.closureLift_card hk hd, A.closureLift_moment hk hd⟩

end NK
