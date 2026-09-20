import NK.WordIntervals
import NK.BinaryArc

/-! # Actual two-block nesting of square interval alphabets

For a perfect-square first modulus P, digits x+P*y carry the affine composition
of their two intervals. The proof includes nonunit roots in the equal-first-digit
case, rather than assuming a block-product transfer theorem.
-/
namespace NK.BlockComposition

variable {P Q : ℕ}

theorem code_lt (P Q x y : ℕ) (hx : x < P) (hy : y < Q) : x + P*y < P*Q := by
  calc
    x + P*y < P + P*y := Nat.add_lt_add_right hx _
    _ = P * (y+1) := by ring
    _ ≤ P*Q := Nat.mul_le_mul_left P hy

theorem diff_same_low (P Q r u v : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hr : r < P) (hu : u < Q) (hv : v < Q) :
    KthPower.diffMod (P*Q) (r+P*u) (r+P*v) = P * KthPower.diffMod Q u v := by
  have hX := code_lt P Q r u hr hu
  have hY := code_lt P Q r v hr hv
  have hd : P * KthPower.diffMod Q u v < P*Q :=
    Nat.mul_lt_mul_of_pos_left (KthPower.diffMod_lt Q u v hQ) hP
  have hshift : (r+P*u+P*KthPower.diffMod Q u v) % (P*Q) = r+P*v := by
    rcases KthPower.diffMod_add Q u v hQ hu hv with h | h
    · have heq : r+P*u+P*KthPower.diffMod Q u v = r+P*v := by nlinarith
      rw [heq, Nat.mod_eq_of_lt hY]
    · have heq : r+P*u+P*KthPower.diffMod Q u v = r+P*v+P*Q := by nlinarith
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hY]
  have h := KthPower.diffMod_unique (P*Q) (r+P*u) (r+P*v)
    (P*KthPower.diffMod Q u v) (Nat.mul_pos hP hQ) hX hY hshift
  rwa [Nat.mod_eq_of_lt hd] at h

/-- A perfect-square factor can be divided out of any square congruence. -/
theorem square_mul_descent (P Q root d : ℕ) (hP : 0 < P) (hroot : P = root ^ 2) :
    (∃ z : ℕ, (z*z) % (P*Q) = P*d) ↔ ∃ w : ℕ, (w*w) % Q = d := by
  constructor
  · rintro ⟨z, hz⟩
    have hdiv : P ∣ z ^ 2 := by
      apply Nat.dvd_of_mod_eq_zero
      have h := congrArg (fun a : ℕ => a % P) hz
      simpa only [pow_two, Nat.mod_mod_of_dvd _ (dvd_mul_right P Q), Nat.mul_mod_right] using h
    obtain ⟨w, hw⟩ := KthPower.word_step3_root_split 2 root P 1 z (by norm_num) hroot (by simpa only [pow_one] using hdiv)
    simp only [pow_one, pow_two] at hw
    rw [hw, Nat.mul_mod_mul_left] at hz
    exact ⟨w, Nat.mul_left_cancel hP hz⟩
  · rintro ⟨w, hw⟩
    refine ⟨root*w, ?_⟩
    have heq : (root*w)*(root*w) = P*(w*w) := by rw [hroot, pow_two]; ring
    rw [heq, Nat.mul_mod_mul_left, hw]

abbrev Point (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) := A.Letter × B.Letter

def encode (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) (p : Point A B) : ℕ :=
  p.1.val + P*p.2.val

noncomputable def pointInterval (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (p : Point A B) : UnitInterval := (A.letterInterval p.1).comp (B.letterInterval p.2)

@[simp] theorem encode_mod (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) (p : Point A B) :
    encode A B p % P = p.1.val := by
  rw [encode, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (A.residue_lt _ p.1.property)]

@[simp] theorem encode_div (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) (hP : 0 < P)
    (p : Point A B) : encode A B p / P = p.2.val := by
  rw [encode, Nat.add_mul_div_left _ _ hP,
    Nat.div_eq_of_lt (A.residue_lt _ p.1.property), Nat.zero_add]

theorem encode_injective (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) (hP : 0 < P) :
    Function.Injective (encode A B) := by
  intro p q heq
  apply Prod.ext
  · apply Subtype.ext
    simpa only [encode_mod] using congrArg (fun x : ℕ => x % P) heq
  · apply Subtype.ext
    simpa only [encode_div A B hP] using congrArg (fun x : ℕ => x / P) heq

theorem encode_bound (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) (p : Point A B) :
    encode A B p < P*Q :=
  code_lt P Q _ _ (A.residue_lt _ p.1.property) (B.residue_lt _ p.2.property)

/-- Every full square arc is ordered by the actually nested intervals. -/
theorem ordered (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (root : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hroot : P = root ^ 2)
    (p q : Point A B) (harc : PowerArc 2 (P*Q) (encode A B p) (encode A B q)) :
    (pointInterval A B p).left + (pointInterval A B p).width ≤ (pointInterval A B q).left := by
  rcases p with ⟨a, u⟩
  rcases q with ⟨c, v⟩
  by_cases hac : a.val = c.val
  · have hac' : a = c := Subtype.ext hac
    subst c
    apply UnitInterval.comp_separated
    apply B.ordered u.val u.property v.val v.property
    have hsq := (BinaryArc.powerArc_iff_square_diff (P*Q) _ _ (Nat.mul_pos hP hQ)
      (encode_bound A B ⟨a,u⟩) (encode_bound A B ⟨a,v⟩)).mp harc
    apply (BinaryArc.powerArc_iff_square_diff Q u.val v.val hQ
      (B.residue_lt _ u.property) (B.residue_lt _ v.property)).mpr
    refine ⟨?_, ?_⟩
    · intro huv
      apply hsq.1
      dsimp [encode]
      rw [huv]
    · obtain ⟨z, hz⟩ := hsq.2
      rw [show encode A B ⟨a,u⟩ = a.val+P*u.val by rfl,
        show encode A B ⟨a,v⟩ = a.val+P*v.val by rfl,
        diff_same_low P Q a.val u.val v.val hP hQ (A.residue_lt _ a.property)
          (B.residue_lt _ u.property) (B.residue_lt _ v.property)] at hz
      exact (square_mul_descent P Q root _ hP hroot).mp ⟨z,hz⟩
  · apply UnitInterval.separated_comp
    apply A.ordered a.val a.property c.val c.property
    obtain ⟨_, z, hz⟩ := harc
    refine ⟨hac, z, ?_⟩
    have h := congrArg (fun x : ℕ => x % P) hz
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right P Q), Nat.mod_mod_of_dvd _ (dvd_mul_right P Q),
      Nat.add_mod, encode_mod A B ⟨a,u⟩, encode_mod A B ⟨c,v⟩] at h
    rw [Nat.add_mod, Nat.mod_eq_of_lt (A.residue_lt _ a.property),
      Nat.mod_eq_of_lt (A.residue_lt _ c.property)]
    exact h

def support (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q) : Finset ℕ :=
  Finset.univ.image (encode A B)

noncomputable def decode (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (x : ℕ) (hx : x ∈ support A B) : Point A B := Classical.choose (Finset.mem_image.mp hx)

theorem encode_decode (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (x : ℕ) (hx : x ∈ support A B) : encode A B (decode A B x hx) = x :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).2

/-- The concrete two-block interval alphabet. -/
noncomputable def nested (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (root : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hroot : P = root ^ 2) : IntervalAlphabet 2 (P*Q) where
  support := support A B
  residue_lt x hx := by rw [← encode_decode A B x hx]; exact encode_bound A B _
  interval x hx := pointInterval A B (decode A B x hx)
  ordered x hx y hy harc := by
    apply ordered A B root hP hQ hroot (decode A B x hx) (decode A B y hy)
    simpa only [encode_decode] using harc

theorem nested_interval (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (root : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hroot : P = root ^ 2)
    (p : Point A B) (hp : encode A B p ∈ (nested A B root hP hQ hroot).support) :
    (nested A B root hP hQ hroot).interval (encode A B p) hp = pointInterval A B p := by
  apply congrArg (pointInterval A B)
  exact encode_injective A B hP (encode_decode A B _ hp)

/-- Nesting multiplies the numbers of selected residues. -/
theorem nested_card (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (root : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hroot : P = root ^ 2) :
    (nested A B root hP hQ hroot).support.card = A.support.card * B.support.card := by
  change (Finset.univ.image (encode A B)).card = _
  rw [Finset.card_image_of_injective _ (encode_injective A B hP), Finset.card_univ]
  simp only [Point, Fintype.card_prod, Fintype.card_coe]

/-- Nesting multiplies the exact moments, for every real exponent. -/
theorem nested_moment (A : IntervalAlphabet 2 P) (B : IntervalAlphabet 2 Q)
    (root : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hroot : P = root ^ 2) (f : ℝ) :
    (nested A B root hP hQ hroot).moment f = A.moment f * B.moment f := by
  classical
  have hsum : (nested A B root hP hQ hroot).moment f =
      ∑ p : Point A B, (pointInterval A B p).width ^ f := by
    symm
    unfold IntervalAlphabet.moment
    refine Finset.sum_bij
      (fun p _ => (⟨encode A B p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩ :
        ↥(nested A B root hP hQ hroot).support)) ?_ ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_attach _ _
    · intro p hp q hq heq
      exact encode_injective A B hP (congrArg Subtype.val heq)
    · intro x _
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp x.property
      exact ⟨p, hp, Subtype.ext heq⟩
    · intro p hp
      rw [nested_interval A B root hP hQ hroot p _]
  rw [hsum, Fintype.sum_prod_type]
  simp only [pointInterval, UnitInterval.comp_width]
  simp_rw [Real.mul_rpow (A.letterInterval _).width_pos.le (B.letterInterval _).width_pos.le]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, IntervalAlphabet.moment,
    Finset.attach_eq_univ, IntervalAlphabet.letterInterval]

end NK.BlockComposition
