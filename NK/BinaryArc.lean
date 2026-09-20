import NK.BinarySquares
import RK.DiffMod

/-! # The full four-branch square relation

Branches are labelled `r + 4*u`, with the first label in `0..3`. The same-label
case retains the complete square relation of the tail, including nonunit squares.
Cross-label arcs are the eight-cycle relation seen through the tail parity.
-/
namespace NK.BinaryArc

/-- The transparent four-branch relation used by the binary two-window split. -/
def fourBranchArc (m r s u v : ℕ) : Prop :=
  (r = s ∧ PowerArc 2 (4 ^ m) u v) ∨
  (r < 3 ∧ s = r + 1 ∧ u % 2 = v % 2) ∨
  (r = 3 ∧ s = 0 ∧ u % 2 ≠ v % 2)

theorem branch_lt (M r u : ℕ) (hr : r < 4) (hu : u < M) :
    r + 4 * u < 4 * M := by omega

@[simp] theorem branch_mod_four (r u : ℕ) (hr : r < 4) :
    (r + 4 * u) % 4 = r := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Tail parity gives the numerical class modulo8. -/
theorem branch_mod_eight (r u : ℕ) (hr : r < 4) :
    (r + 4 * u) % 8 = r + 4 * (u % 2) := by
  have hu : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hm : (4 * u) % 8 = 4 * (u % 2) := Nat.mul_mod_mul_left 4 u 2
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : r < 8), hm]
  exact Nat.mod_eq_of_lt (by omega)

/-- The numerical successor relation modulo8 is precisely the labelled cycle. -/
theorem branch_successor_iff (r s u v : ℕ) (hr : r < 4) (hs : s < 4) :
    (r + 4 * u + 1) % 8 = (s + 4 * v) % 8 ↔
      (r < 3 ∧ s = r + 1 ∧ u % 2 = v % 2) ∨
      (r = 3 ∧ s = 0 ∧ u % 2 ≠ v % 2) := by
  have hu : u % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hv : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [Nat.add_mod, branch_mod_eight r u hr, branch_mod_eight s v hs]
  interval_cases r <;> interval_cases s <;> interval_cases u % 2 <;>
    interval_cases v % 2 <;> norm_num

/-- A bounded-residue additive power arc is exactly a square difference residue. -/
theorem powerArc_iff_square_diff (M X Y : ℕ) (hM : 0 < M) (hX : X < M) (hY : Y < M) :
    PowerArc 2 M X Y ↔ X ≠ Y ∧ ∃ z : ℕ, (z * z) % M = KthPower.diffMod M X Y := by
  constructor
  · rintro ⟨hne, z, hz⟩
    refine ⟨hne, z, ?_⟩
    rw [Nat.mod_eq_of_lt hY] at hz
    simpa only [pow_two] using (KthPower.diffMod_unique M X Y (z ^ 2) hM hX hY hz).symm
  · rintro ⟨hne, z, hz⟩
    refine ⟨hne, z, ?_⟩
    have hd : (X + KthPower.diffMod M X Y) % M = Y := by
      rcases KthPower.diffMod_add M X Y hM hX hY with h | h
      · rw [h, Nat.mod_eq_of_lt hY]
      · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hY]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (KthPower.diffMod_lt M X Y hM)] at hd
    rw [Nat.add_mod, pow_two, hz, Nat.mod_eq_of_lt hY]
    exact hd

/-- Within one label, the modular difference factors exactly by4. -/
theorem diffMod_same_branch (m r u v : ℕ) (hr : r < 4)
    (hu : u < 4 ^ m) (hv : v < 4 ^ m) :
    KthPower.diffMod (4 ^ (m+1)) (r + 4*u) (r + 4*v) =
      4 * KthPower.diffMod (4 ^ m) u v := by
  have hM : 0 < 4 ^ m := by positivity
  have hpow : 4 ^ (m+1) = 4 * 4 ^ m := by rw [pow_succ, mul_comm]
  have hX : r + 4*u < 4 ^ (m+1) := by rw [hpow]; exact branch_lt _ _ _ hr hu
  have hY : r + 4*v < 4 ^ (m+1) := by rw [hpow]; exact branch_lt _ _ _ hr hv
  have hd : 4 * KthPower.diffMod (4 ^ m) u v < 4 ^ (m+1) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left (KthPower.diffMod_lt _ u v hM) (by norm_num)
  have hshift : (r + 4*u + 4 * KthPower.diffMod (4 ^ m) u v) % 4 ^ (m+1) = r + 4*v := by
    rcases KthPower.diffMod_add (4 ^ m) u v hM hu hv with h | h
    · have heq : r + 4*u + 4 * KthPower.diffMod (4 ^ m) u v = r + 4*v := by omega
      rw [heq, Nat.mod_eq_of_lt hY]
    · have heq : r + 4*u + 4 * KthPower.diffMod (4 ^ m) u v = r + 4*v + 4 ^ (m+1) := by
        rw [hpow]
        omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hY]
  have h := KthPower.diffMod_unique (4 ^ (m+1)) (r + 4*u) (r + 4*v)
    (4 * KthPower.diffMod (4 ^ m) u v) (by positivity) hX hY hshift
  rwa [Nat.mod_eq_of_lt hd] at h

/-- Same-label arcs descend to exactly the full tail graph. -/
theorem same_branch_iff (m r u v : ℕ) (hr : r < 4)
    (hu : u < 4 ^ m) (hv : v < 4 ^ m) :
    PowerArc 2 (4 ^ (m+1)) (r + 4*u) (r + 4*v) ↔ PowerArc 2 (4 ^ m) u v := by
  have hpow : 4 ^ (m+1) = 4 * 4 ^ m := by rw [pow_succ, mul_comm]
  have hX : r + 4*u < 4 ^ (m+1) := by rw [hpow]; exact branch_lt _ _ _ hr hu
  have hY : r + 4*v < 4 ^ (m+1) := by rw [hpow]; exact branch_lt _ _ _ hr hv
  have hd := KthPower.diffMod_lt (4 ^ m) u v (by positivity)
  have hd4 : 4 * KthPower.diffMod (4 ^ m) u v < 4 ^ (m+1) := by rw [hpow]; omega
  have hdescent := BinarySquares.square_four_mul_descent m (KthPower.diffMod (4 ^ m) u v)
  rw [Nat.mod_eq_of_lt hd4, Nat.mod_eq_of_lt hd] at hdescent
  rw [powerArc_iff_square_diff _ _ _ (by positivity) hX hY,
    diffMod_same_branch m r u v hr hu hv, hdescent,
    powerArc_iff_square_diff _ _ _ (by positivity) hu hv]
  have hne : r + 4*u ≠ r + 4*v ↔ u ≠ v := by omega
  rw [hne]

/-- A numerical successor modulo8 is a square arc at every higher binary modulus. -/
theorem powerArc_of_successor_mod_eight (n X Y : ℕ) (hn : 3 ≤ n)
    (hX : X < 2 ^ n) (hY : Y < 2 ^ n)
    (hsucc : (X + 1) % 8 = Y % 8) : PowerArc 2 (2 ^ n) X Y := by
  have hM : 0 < 2 ^ n := by positivity
  have hdiv : 8 ∣ 2 ^ n := by simpa using Nat.pow_dvd_pow 2 hn
  have hshift : (X + KthPower.diffMod (2 ^ n) X Y) % 8 = Y % 8 := by
    rcases KthPower.diffMod_add (2 ^ n) X Y hM hX hY with h | h
    · rw [h]
    · rw [h, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero, Nat.mod_mod]
  have hcancel : Nat.ModEq 8 (X + KthPower.diffMod (2 ^ n) X Y) (X + 1) :=
    hshift.trans hsucc.symm
  have hD8 : KthPower.diffMod (2 ^ n) X Y % 8 = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 8)] using
      Nat.ModEq.add_left_cancel' X hcancel
  have hD2 : KthPower.diffMod (2 ^ n) X Y % 2 = 1 := by
    have h := congrArg (fun x : ℕ => x % 2) hD8
    simpa only [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8),
      Nat.mod_eq_of_lt (by norm_num : 1 < 2)] using h
  have hne : X ≠ Y := by
    intro h
    subst Y
    simp [KthPower.diffMod] at hD8
  have hroot := (BinarySquares.odd_square_iff_mod_eight n
    (KthPower.diffMod (2 ^ n) X Y) hn hD2).mpr hD8
  apply (powerArc_iff_square_diff (2 ^ n) X Y hM hX hY).mpr
  refine ⟨hne, ?_⟩
  obtain ⟨z, hz⟩ := hroot
  refine ⟨z, ?_⟩
  simpa only [Nat.mod_eq_of_lt (KthPower.diffMod_lt _ X Y hM)] using hz

/-- Distinct first labels force an odd square, hence numerical successor modulo8. -/
theorem cross_arc_successor (m r s u v : ℕ) (hm : 1 ≤ m)
    (hr : r < 4) (hs : s < 4) (hrs : r ≠ s)
    (harc : PowerArc 2 (4 ^ (m+1)) (r + 4*u) (s + 4*v)) :
    (r + 4*u + 1) % 8 = (s + 4*v) % 8 := by
  obtain ⟨_, z, hz⟩ := harc
  have hd4 : 4 ∣ 4 ^ (m+1) := dvd_pow_self 4 (by omega)
  have hd16 : 16 ∣ 4 ^ (m+1) := by
    simpa using Nat.pow_dvd_pow 4 (show 2 ≤ m+1 by omega)
  have hd8 : 8 ∣ 4 ^ (m+1) := dvd_trans (by norm_num : 8 ∣ 16) hd16
  have hc4 : (r + 4*u + z*z) % 4 = (s + 4*v) % 4 := by
    have h := congrArg (fun x : ℕ => x % 4) hz
    simpa only [pow_two, Nat.mod_mod_of_dvd _ hd4] using h
  have hroot4 : (z*z) % 4 ≠ 0 := by
    intro hzero
    rw [Nat.add_mod, branch_mod_four r u hr, branch_mod_four s v hs,
      hzero, Nat.add_zero, Nat.mod_eq_of_lt hr] at hc4
    exact hrs hc4
  have hroot8 : (z*z) % 8 = 1 := by
    rcases BinarySquares.square_mod_eight z with h0 | h1 | h4
    · exfalso
      apply hroot4
      have h := congrArg (fun x : ℕ => x % 4) h0
      simpa only [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 8), Nat.zero_mod] using h
    · exact h1
    · exfalso
      apply hroot4
      have h := congrArg (fun x : ℕ => x % 4) h4
      simpa only [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 8), Nat.mod_self] using h
  have hc8 : (r + 4*u + z*z) % 8 = (s + 4*v) % 8 := by
    have h := congrArg (fun x : ℕ => x % 8) hz
    simpa only [pow_two, Nat.mod_mod_of_dvd _ hd8] using h
  rw [Nat.add_mod, hroot8] at hc8
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by norm_num : 1 < 8)]
  exact hc8

/-- The cross-label arc relation, with both existence and exclusion directions. -/
theorem cross_branch_iff (m r s u v : ℕ) (hm : 1 ≤ m)
    (hr : r < 4) (hs : s < 4) (hu : u < 4 ^ m) (hv : v < 4 ^ m) (hrs : r ≠ s) :
    PowerArc 2 (4 ^ (m+1)) (r + 4*u) (s + 4*v) ↔
      (r < 3 ∧ s = r + 1 ∧ u % 2 = v % 2) ∨
      (r = 3 ∧ s = 0 ∧ u % 2 ≠ v % 2) := by
  constructor
  · intro harc
    exact (branch_successor_iff r s u v hr hs).mp (cross_arc_successor m r s u v hm hr hs hrs harc)
  · intro hcycle
    have hsucc := (branch_successor_iff r s u v hr hs).mpr hcycle
    have hpow : 4 ^ (m+1) = 4 * 4 ^ m := by rw [pow_succ, mul_comm]
    have hbase : 2 ^ (2 * (m+1)) = 4 ^ (m+1) := by rw [pow_mul]; norm_num
    have hX : r + 4*u < 2 ^ (2 * (m+1)) := by rw [hbase, hpow]; exact branch_lt _ _ _ hr hu
    have hY : s + 4*v < 2 ^ (2 * (m+1)) := by rw [hbase, hpow]; exact branch_lt _ _ _ hs hv
    have h := powerArc_of_successor_mod_eight (2 * (m+1)) (r + 4*u) (s + 4*v)
      (by omega) hX hY hsucc
    simpa only [hbase] using h

/-- The complete full-image square relation for the four binary branches. -/
theorem powerArc_fourBranch_iff (m r s u v : ℕ) (hm : 1 ≤ m)
    (hr : r < 4) (hs : s < 4) (hu : u < 4 ^ m) (hv : v < 4 ^ m) :
    PowerArc 2 (4 ^ (m+1)) (r + 4*u) (s + 4*v) ↔ fourBranchArc m r s u v := by
  by_cases hrs : r = s
  · subst s
    rw [same_branch_iff m r u v hr hu hv]
    unfold fourBranchArc
    constructor
    · intro h
      exact Or.inl ⟨rfl, h⟩
    · rintro (⟨_, h⟩ | ⟨_, h, _⟩ | ⟨h3, h0, _⟩)
      · exact h
      · omega
      · omega
  · rw [cross_branch_iff m r s u v hm hr hs hu hv hrs]
    simp only [fourBranchArc, hrs, false_and, false_or]

end NK.BinaryArc
