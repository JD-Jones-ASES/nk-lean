import NK.UnitConductor
import NK.RetainedFibers
import NK.WordIntervals

/-! # Exact first-difference graphs in prime-power blocks

A block is one base-p^k digit, and words are written low block first. The forward
arc projection holds for every perfect-power base. Outside binary squares, the
unit conductor proves the converse, including all nonunit differences: the
common lower blocks are factored out before lifting the remaining unit root.
-/
namespace NK

/-- For bounded residues, a power arc is exactly a power representation of the
canonical modular difference. -/
theorem powerArc_iff_pow_diff (k m x y : ℕ) (hm : 0 < m) (hx : x < m) (hy : y < m) :
    PowerArc k m x y ↔ x ≠ y ∧ ∃ z : ℕ, z ^ k % m = KthPower.diffMod m x y := by
  constructor
  · rintro ⟨hne, z, hz⟩
    rw [Nat.mod_eq_of_lt hy] at hz
    exact ⟨hne, z, (KthPower.diffMod_unique m x y (z ^ k) hm hx hy hz).symm⟩
  · rintro ⟨hne, z, hz⟩
    refine ⟨hne, z, ?_⟩
    rw [Nat.add_mod, hz, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    rcases KthPower.diffMod_add m x y hm hx hy with h | h
    · rw [h, Nat.mod_eq_of_lt hy]
    · rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

/-- A nonzero kth power modulo p^k is necessarily a unit. -/
theorem nonzero_power_mod_block_is_unit (p k d : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hd : d % p ^ k ≠ 0) (hroot : ∃ z : ℕ, z ^ k % p ^ k = d % p ^ k) : ¬ p ∣ d := by
  rintro hpd
  obtain ⟨z, hz⟩ := hroot
  have hdiv : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hzmod : z ^ k % p = 0 := by
    have hh := congrArg (fun a : ℕ => a % p) hz
    simpa only [Nat.mod_mod_of_dvd _ hdiv, Nat.mod_eq_zero_of_dvd hpd] using hh
  have hpz : p ∣ z := hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hzmod)
  have hpzk : p ^ k ∣ z ^ k := pow_dvd_pow_of_dvd hpz k
  exact hd (hz.symm.trans (Nat.mod_eq_zero_of_dvd hpzk))

/-- A first differing block that is a local arc lifts to a full modular arc.
The factored difference may be nonunit; only its remaining quotient is lifted. -/
theorem powerArc_of_first_block (p k e x y j : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e)
    (hx : x < (p ^ k) ^ e) (hy : y < (p ^ k) ^ e) (hj : j < e)
    (hlow : ∀ i < j, KthPower.digit (p ^ k) i x = KthPower.digit (p ^ k) i y)
    (harc : PowerArc k (p ^ k) (KthPower.digit (p ^ k) j x)
      (KthPower.digit (p ^ k) j y)) : PowerArc k ((p ^ k) ^ e) x y := by
  let P := p ^ k
  have hP : 2 ≤ P := by
    have hpk : p ≤ p ^ k := by
      simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hk
    exact hp.two_le.trans hpk
  have hPpos : 0 < P := by omega
  have hMpos : 0 < P ^ e := pow_pos hPpos _
  have hxy : x ≠ y := by intro h; subst y; exact harc.1 rfl
  let D := KthPower.diffMod (P ^ e) x y
  obtain ⟨hdvd, _⟩ := KthPower.word_step0_exact_dvd k P e x y j hk hP he hx hy hj harc.1 hlow
  obtain ⟨d, hd⟩ := hdvd
  change D = P ^ j * d at hd
  have hlead : d % P = KthPower.diffMod P (KthPower.digit P j x)
      (KthPower.digit P j y) := by
    have hh := KthPower.word_step1_leading_digit k P e x y j hk hP he hx hy hj hlow
    change D / P ^ j % P = _ at hh
    rwa [hd, Nat.mul_div_cancel_left _ (pow_pos hPpos j)] at hh
  have hxj := KthPower.digit_lt P j x hPpos
  have hyj := KthPower.digit_lt P j y hPpos
  obtain ⟨_, z, hz⟩ := (powerArc_iff_pow_diff k P _ _ hPpos hxj hyj).mp harc
  have hroot : ∃ z : ℕ, z ^ k % P = d % P := ⟨z, hz.trans hlead.symm⟩
  have hdnonzero : d % P ≠ 0 := by
    rw [hlead]
    exact KthPower.diffMod_ne_zero P _ _ hxj hyj harc.1
  have hunit : ¬ p ∣ d := nonzero_power_mod_block_is_unit p k d hp hk hdnonzero hroot
  have hke : k ≤ k * (e - j) := by
    simpa only [mul_one] using Nat.mul_le_mul_left k (show 1 ≤ e - j by omega)
  obtain ⟨w, hw⟩ := (unitPower_stabilizes_block p k d (k * (e - j)) hp hk hunit
    hexception hke).mpr hroot
  simp only [pow_mul] at hw
  have hsplit : P ^ e = P ^ j * P ^ (e - j) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj)]
  have hdlt : d < P ^ (e - j) := by
    have hDlt := KthPower.diffMod_lt (P ^ e) x y hMpos
    change D < P ^ e at hDlt
    rw [hd, hsplit] at hDlt
    exact (Nat.mul_lt_mul_left (pow_pos hPpos j)).mp hDlt
  rw [Nat.mod_eq_of_lt hdlt] at hw
  apply (powerArc_iff_pow_diff k (P ^ e) x y hMpos hx hy).mpr
  refine ⟨hxy, p ^ j * w, ?_⟩
  change (p ^ j * w) ^ k % P ^ e = D
  have hpow : (p ^ j * w) ^ k = P ^ j * w ^ k := by
    rw [mul_pow]
    dsimp only [P]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j k]
  rw [hpow, hsplit, Nat.mul_mod_mul_left, hw, hd]

/-- Complete low-to-high block words; no digits are deleted. -/
def fullBlockDigits (k p e x : ℕ) : List ℕ := retainedDigits 1 (p ^ k) e x

@[simp] theorem fullBlockDigits_length (k p e x : ℕ) :
    (fullBlockDigits k p e x).length = e := by simp [fullBlockDigits]

theorem fullBlockDigits_getD (k p e x j : ℕ) (hj : j < e) :
    (fullBlockDigits k p e x).getD j 0 = KthPower.digit (p ^ k) j x := by
  simpa only [fullBlockDigits, one_mul] using retainedDigits_getD 1 (p ^ k) e x j hj

/-- Exact graph description, excluding the actual binary-square lookahead case. -/
theorem powerArc_iff_firstDifference_block (p k e x y : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e)
    (hx : x < (p ^ k) ^ e) (hy : y < (p ^ k) ^ e) :
    PowerArc k ((p ^ k) ^ e) x y ↔
      FirstDifferencePowerArc k (p ^ k) (fullBlockDigits k p e x) (fullBlockDigits k p e y) := by
  have hP : 2 ≤ p ^ k := hp.two_le.trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hk)
  constructor
  · intro harc
    obtain ⟨j, hj, hlow, hjArc⟩ := powerArc_least_digit k p (p ^ k) e x y hk hP rfl he hx hy harc
    refine ⟨by simp, j, by simpa using hj, ?_, ?_⟩
    · intro i hi
      simpa only [fullBlockDigits_getD k p e x i (by omega),
        fullBlockDigits_getD k p e y i (by omega)] using hlow i hi
    · simpa only [fullBlockDigits_getD k p e x j hj,
        fullBlockDigits_getD k p e y j hj] using hjArc
  · rintro ⟨_, j, hj, hlow, harc⟩
    have hj' : j < e := by simpa using hj
    apply powerArc_of_first_block p k e x y j hp hk hexception he hx hy hj'
    · intro i hi
      simpa only [fullBlockDigits_getD k p e x i (by omega),
        fullBlockDigits_getD k p e y i (by omega)] using hlow i hi
    · simpa only [fullBlockDigits_getD k p e x j hj',
        fullBlockDigits_getD k p e y j hj'] using harc

/-- Literal base-b digits of a bounded integer, with the least digit first. -/
def blockWord (b e : ℕ) (hb : 2 ≤ b) (x : Fin (b ^ e)) : Fin e → Fin b :=
  fun j => ⟨KthPower.digit b j.val x.val, KthPower.digit_lt b j.val x.val (by omega)⟩

theorem blockWord_injective (b e : ℕ) (hb : 2 ≤ b) :
    Function.Injective (blockWord b e hb) := by
  intro x y h
  apply Fin.ext
  apply KthPower.eq_of_digits_eq b e x.val y.val hb x.isLt y.isLt
  intro j hj
  exact congrArg Fin.val (congrFun h ⟨j, hj⟩)

theorem blockWord_surjective (b e : ℕ) (hb : 2 ≤ b) :
    Function.Surjective (blockWord b e hb) := by
  intro v
  let w : List ℕ := List.ofFn (fun i : Fin e => (v i).val)
  have hlen : w.length = e := by simp [w]
  have hvalid : ∀ a ∈ w, a < b := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (v i).isLt
  obtain ⟨x, hx, hword⟩ := exists_retainedDigits_eq 1 b e w (by omega) hb hlen hvalid
  have hx' : x < b ^ e := by simpa only [one_mul] using hx
  refine ⟨⟨x, hx'⟩, ?_⟩
  have hfun : (fun i : Fin e => KthPower.digit b i.val x) = fun i => (v i).val := by
    apply List.ofFn_injective
    simpa only [retainedDigits, one_mul, w] using hword
  funext j
  exact Fin.ext (congrFun hfun j)

/-- All fixed-length block words occur exactly once, including words with
leading zero blocks. -/
noncomputable def blockWordEquiv (b e : ℕ) (hb : 2 ≤ b) :
    Fin (b ^ e) ≃ (Fin e → Fin b) :=
  Equiv.ofBijective (blockWord b e hb)
    ⟨blockWord_injective b e hb, blockWord_surjective b e hb⟩

@[simp] theorem blockWordEquiv_apply (b e : ℕ) (hb : 2 ≤ b)
    (x : Fin (b ^ e)) (j : Fin e) :
    (blockWordEquiv b e hb x j).val = KthPower.digit b j.val x.val := rfl

/-- The finite residue-to-word bijection preserves and reflects every arc.
This is the exact finite digraph isomorphism used by the capacity identity. -/
theorem powerArc_iff_blockWord (p k e : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e)
    (x y : Fin ((p ^ k) ^ e))
    (hP : 2 ≤ p ^ k := hp.two_le.trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hk)) :
    PowerArc k ((p ^ k) ^ e) x.val y.val ↔
      ∃ j : Fin e,
        (∀ i : Fin e, i < j → blockWordEquiv (p ^ k) e hP x i =
          blockWordEquiv (p ^ k) e hP y i) ∧
        PowerArc k (p ^ k) (blockWordEquiv (p ^ k) e hP x j).val
          (blockWordEquiv (p ^ k) e hP y j).val := by
  rw [powerArc_iff_firstDifference_block p k e x.val y.val hp hk hexception he x.isLt y.isLt]
  constructor
  · rintro ⟨_, j, hj, hlow, harc⟩
    have hj' : j < e := by simpa using hj
    refine ⟨⟨j, hj'⟩, ?_, ?_⟩
    · intro i hi
      apply Fin.ext
      simp only [blockWordEquiv_apply]
      simpa only [fullBlockDigits_getD k p e x.val i.val i.isLt,
        fullBlockDigits_getD k p e y.val i.val i.isLt] using hlow i.val hi
    · simpa only [blockWordEquiv_apply, fullBlockDigits_getD k p e x.val j hj',
        fullBlockDigits_getD k p e y.val j hj'] using harc
  · rintro ⟨j, hlow, harc⟩
    refine ⟨by simp, j.val, by simp, ?_, ?_⟩
    · intro i hi
      have hi' : i < e := by omega
      have h := congrArg Fin.val (hlow ⟨i, hi'⟩ hi)
      simpa only [blockWordEquiv_apply, fullBlockDigits_getD k p e x.val i hi',
        fullBlockDigits_getD k p e y.val i hi'] using h
    · simpa only [blockWordEquiv_apply, fullBlockDigits_getD k p e x.val j.val j.isLt,
        fullBlockDigits_getD k p e y.val j.val j.isLt] using harc

/-- The excluded pair really fails: the first base-four block permits the
arc from zero to five, whereas the full modulus sixteen forbids it. -/
theorem binary_square_block_graph_counterexample :
    FirstDifferencePowerArc 2 4 (fullBlockDigits 2 2 2 0) (fullBlockDigits 2 2 2 5) ∧
      ¬ PowerArc 2 16 0 5 := by
  constructor
  · refine ⟨by decide, 0, by decide, ?_, ?_⟩
    · intro i hi
      omega
    · change PowerArc 2 4 0 1
      exact ⟨by decide, 1, by decide⟩
  · rintro ⟨_, z, hz⟩
    apply binary_square_lookahead_counterexample.2
    exact ⟨z, by simpa only [Nat.zero_add] using hz⟩

end NK
