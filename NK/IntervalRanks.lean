import NK.Intervals
import NK.RankedTransfer
import RK.DiffMod

/-! Ordered intervals of a common positive minimum width give a finite
ranked block by flooring left endpoints and reversing the ranks. -/
namespace NK

/-- RK's residue-power predicate implies the full additive power arc. -/
theorem powerArc_of_nonzeroPowerMod (k m x y : ℕ) (hx : x < m) (hy : y < m)
    (hne : x ≠ y) (hp : KthPower.IsNonzeroPowerMod k m (KthPower.diffMod m x y)) :
    PowerArc k m x y := by
  have hm : 0 < m := by omega
  obtain ⟨_, z, _, hz⟩ := hp
  have hd : KthPower.diffMod m x y < m := KthPower.diffMod_lt m x y hm
  rw [Nat.mod_eq_of_lt hd] at hz
  refine ⟨hne, z, ?_⟩
  rw [Nat.add_mod, hz, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  rcases KthPower.diffMod_add m x y hm hx hy with h | h
  · rw [h, Nat.mod_eq_of_lt hy]
  · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

/-- The integer height required at resolution ε. -/
noncomputable def intervalHeight (ε : ℝ) : ℕ := ⌈1 / ε⌉₊

/-- Decreasing ranks match the ranked-block interface inherited from RK. -/
noncomputable def intervalRank {k m : ℕ} (A : IntervalAlphabet k m) (ε : ℝ) (x : ℕ) : ℕ :=
  if hx : x ∈ A.support then intervalHeight ε - 1 - ⌊(A.interval x hx).left / ε⌋₊ else 0

theorem intervalHeight_pos (ε : ℝ) (hε : 0 < ε) : 0 < intervalHeight ε := by
  exact Nat.ceil_pos.mpr (one_div_pos.mpr hε)

/-- Rounding loses only a common height; it preserves every full power arc. -/
theorem IntervalAlphabet.rankedBlock {k m : ℕ} (A : IntervalAlphabet k m)
    (ε : ℝ) (hε : 0 < ε)
    (hw : ∀ x (hx : x ∈ A.support), ε ≤ (A.interval x hx).width) :
    KthPower.RankedBlock k m A.support (intervalRank A ε) (intervalHeight ε) := by
  have hH := intervalHeight_pos ε hε
  refine ⟨A.residue_lt, ?_, ?_⟩
  · intro x hx
    simp only [intervalRank, dif_pos hx]
    omega
  · intro x hx y hy hne hp
    have horder := A.ordered x hx y hy
      (powerArc_of_nonzeroPowerMod k m x y (A.residue_lt x hx) (A.residue_lt y hy) hne hp)
    have hlt := UnitInterval.floor_rank_lt_of_separated (A.interval x hx) (A.interval y hy)
      ε hε (hw x hx) horder
    have hxb := UnitInterval.floor_rank_lt (A.interval x hx) ε hε
    have hyb := UnitInterval.floor_rank_lt (A.interval y hy) ε hε
    simp only [intervalRank, dif_pos hx, dif_pos hy]
    change _ < intervalHeight ε at hxb hyb
    omega

/-- A one-block interval criterion, useful after the multi-component stopping
construction has produced its combined modulus and minimum interval width. -/
theorem IntervalAlphabet.powerLowerBound {k m : ℕ} (A : IntervalAlphabet k m)
    (n : ℕ) (hk : 1 ≤ k) (hm : m = n ^ k) (ε : ℝ) (hε : 0 < ε)
    (hw : ∀ x (hx : x ∈ A.support), ε ≤ (A.interval x hx).width)
    (hbase : 2 ≤ m * intervalHeight ε) (hne : A.support.Nonempty)
    (α : ℝ) (hα : 0 ≤ α)
    (hcount : ((m * intervalHeight ε : ℕ) : ℝ) ^ α ≤ A.support.card) :
    PowerLowerBound k α :=
  powerLowerBound_of_rankedBlock k n m hk hm A.support (intervalRank A ε)
    (intervalHeight ε) (A.rankedBlock ε hε hw) (intervalHeight_pos ε hε)
    hbase (Finset.one_le_card.mpr hne) α hα hcount

end NK
