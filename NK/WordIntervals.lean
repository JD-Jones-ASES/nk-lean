import NK.StoppingWords
import NK.IntervalRanks
import RK.LemmaB

/-! # Ordered interval alphabets from equal-length words

The first letter is both the least significant base digit and the outermost
affine interval map. The arithmetic step uses the proved perfect-power digit
lemmas from RK.LemmaB; it does not use a ranked-word transfer assumption.
-/
namespace NK
namespace IntervalAlphabet

variable {k b : ℕ}

abbrev Letter (A : IntervalAlphabet k b) := {x : ℕ // x ∈ A.support}

/-- Low-to-high base-b encoding, including leading zero letters. -/
def encode (A : IntervalAlphabet k b) : List A.Letter → ℕ
  | [] => 0
  | a :: v => a.val + b * A.encode v

/-- The letter's assigned interval. -/
noncomputable def letterInterval (A : IntervalAlphabet k b) (a : A.Letter) : UnitInterval :=
  A.interval a.val a.property

/-- Actual affine composition of the intervals assigned to the letters. -/
noncomputable def wordInterval (A : IntervalAlphabet k b) (v : List A.Letter) : UnitInterval :=
  UnitInterval.word (v.map A.letterInterval)

@[simp] theorem encode_nil (A : IntervalAlphabet k b) : A.encode [] = 0 := rfl
@[simp] theorem encode_cons (A : IntervalAlphabet k b) (a : A.Letter) (v : List A.Letter) :
    A.encode (a :: v) = a.val + b * A.encode v := rfl

@[simp] theorem wordInterval_cons (A : IntervalAlphabet k b) (a : A.Letter)
    (v : List A.Letter) :
    A.wordInterval (a :: v) = (A.letterInterval a).comp (A.wordInterval v) := rfl

theorem encode_lt (A : IntervalAlphabet k b) (v : List A.Letter) :
    A.encode v < b ^ v.length := by
  induction v with
  | nil => simp
  | cons a v ih =>
    simp only [encode_cons, List.length_cons]
    calc
      a.val + b * A.encode v < b + b * A.encode v :=
        Nat.add_lt_add_right (A.residue_lt a.val a.property) _
      _ = b * (A.encode v + 1) := by ring
      _ ≤ b * b ^ v.length := Nat.mul_le_mul_left b ih
      _ = b ^ (v.length + 1) := by rw [pow_succ, mul_comm]

@[simp] theorem encode_cons_mod (A : IntervalAlphabet k b) (a : A.Letter)
    (v : List A.Letter) : A.encode (a :: v) % b = a.val := by
  rw [encode_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (A.residue_lt a.val a.property)]

@[simp] theorem encode_cons_div (A : IntervalAlphabet k b) (hb : 0 < b)
    (a : A.Letter) (v : List A.Letter) : A.encode (a :: v) / b = A.encode v := by
  rw [encode_cons, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt (A.residue_lt a.val a.property), zero_add]

@[simp] theorem digit_encode_zero (A : IntervalAlphabet k b) (a : A.Letter)
    (v : List A.Letter) : KthPower.digit b 0 (A.encode (a :: v)) = a.val := by
  rw [KthPower.digit, pow_zero, Nat.div_one]
  exact A.encode_cons_mod a v

@[simp] theorem digit_encode_succ (A : IntervalAlphabet k b) (hb : 0 < b)
    (a : A.Letter) (v : List A.Letter) (j : ℕ) :
    KthPower.digit b (j+1) (A.encode (a :: v)) = KthPower.digit b j (A.encode v) := by
  rw [KthPower.digit_succ, A.encode_cons_div hb]

/-- Equal-length words have distinct codes; leading zeroes cause no collision. -/
theorem encode_injective_equal_length (A : IntervalAlphabet k b) (hb : 0 < b)
    (v t : List A.Letter) (hlen : v.length = t.length) (hcode : A.encode v = A.encode t) :
    v = t := by
  induction v generalizing t with
  | nil =>
    have ht : t = [] := List.length_eq_zero_iff.mp hlen.symm
    exact ht.symm
  | cons a v ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      have hac : a = c := by
        apply Subtype.ext
        have h := congrArg (fun x => x % b) hcode
        simpa only [encode_cons_mod] using h
      subst c
      congr 1
      apply ih t (by simpa using hlen)
      have h := congrArg (fun x => x / b) hcode
      simpa only [encode_cons_div A hb] using h

/-- The affine interval width is exactly the stopping-tree word width. -/
theorem wordInterval_width (A : IntervalAlphabet k b) (v : List A.Letter) :
    (A.wordInterval v).width = StoppingWords.width (fun a => (A.letterInterval a).width) v := by
  rw [StoppingWords.width_eq_prod]
  simp only [wordInterval, UnitInterval.word_width, List.map_map, Function.comp_def]

/-- A prescribed first differing digit orders the actual composed intervals. -/
theorem wordInterval_ordered_at (A : IntervalAlphabet k b) (hb : 0 < b)
    (v t : List A.Letter) (j : ℕ) (hlen : v.length = t.length) (hj : j < v.length)
    (hlow : ∀ i < j, KthPower.digit b i (A.encode v) = KthPower.digit b i (A.encode t))
    (harc : PowerArc k b (KthPower.digit b j (A.encode v))
      (KthPower.digit b j (A.encode t))) :
    (A.wordInterval v).left + (A.wordInterval v).width ≤ (A.wordInterval t).left := by
  induction v generalizing t j with
  | nil => simp at hj
  | cons a v ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      cases j with
      | zero =>
        have hac : PowerArc k b a.val c.val := by simpa only [digit_encode_zero] using harc
        have hsep := A.ordered a.val a.property c.val c.property hac
        exact UnitInterval.separated_comp (A.letterInterval a) (A.letterInterval c)
          (A.wordInterval v) (A.wordInterval t) hsep
      | succ j =>
        have hac : a = c := by
          apply Subtype.ext
          simpa only [digit_encode_zero] using hlow 0 (by omega)
        subst c
        have htail := ih t j (by simpa using hlen) (by simpa using hj)
          (fun i hi => by simpa only [digit_encode_succ A hb] using hlow (i+1) (by omega))
          (by simpa only [digit_encode_succ A hb] using harc)
        exact UnitInterval.comp_separated (A.letterInterval a)
          (A.wordInterval v) (A.wordInterval t) htail

end IntervalAlphabet

/-- In a perfect-power base, a full power arc induces an arc at its least
unequal digit. This is the arithmetic spine needed for interval words. -/
theorem powerArc_least_digit (k n b L X Y : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b)
    (hbase : b = n ^ k) (hL : 1 ≤ L) (hX : X < b ^ L) (hY : Y < b ^ L)
    (harc : PowerArc k (b ^ L) X Y) :
    ∃ j, j < L ∧ (∀ i < j, KthPower.digit b i X = KthPower.digit b i Y) ∧
      PowerArc k b (KthPower.digit b j X) (KthPower.digit b j Y) := by
  obtain ⟨hne, z, hcong⟩ := harc
  have hb0 : 0 < b := by omega
  have hbL : 0 < b ^ L := pow_pos hb0 _
  rw [Nat.mod_eq_of_lt hY] at hcong
  have hc : z ^ k % b ^ L = KthPower.diffMod (b ^ L) X Y :=
    (KthPower.diffMod_unique (b ^ L) X Y (z ^ k) hbL hX hY hcong).symm
  have hd0 := KthPower.diffMod_ne_zero (b ^ L) X Y hX hY hne
  have hdlt := KthPower.diffMod_lt (b ^ L) X Y hbL
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp only [zero_pow (by omega : k ≠ 0), Nat.zero_mod] at hc
    exact hd0 hc.symm
  obtain ⟨j, hj, hjne, hjlow⟩ :=
    KthPower.exists_least_digit_ne_of_lt k b L X Y hk hb hX hY hne
  obtain ⟨hdvd1, hdvd2⟩ :=
    KthPower.word_step0_exact_dvd k b L X Y j hk hb hL hX hY hj hjne hjlow
  have hdiv := KthPower.word_step2_pow_dvd_pow k b L j z
    (KthPower.diffMod (b ^ L) X Y) hj hc hdvd1
  obtain ⟨u, hu⟩ := KthPower.word_step3_root_split k n b j z hk hbase hdiv
  have hlam : z ^ k = KthPower.diffMod (b ^ L) X Y + (z ^ k / b ^ L) * b ^ L := by
    rw [← hc]
    exact (Nat.mod_add_div' _ _).symm
  have hpow := KthPower.word_step4_leading_power k b L j z (z ^ k / b ^ L) u
    (KthPower.diffMod (b ^ L) X Y) hk hb hL hd0 hdlt hz hj hlam hu hdvd1 hdvd2
  rw [KthPower.word_step1_leading_digit k b L X Y j hk hb hL hX hY hj hjlow] at hpow
  exact ⟨j, hj, hjlow, powerArc_of_nonzeroPowerMod k b _ _
    (KthPower.digit_lt b j X hb0) (KthPower.digit_lt b j Y hb0) hjne hpow⟩

namespace IntervalAlphabet

variable {k b : ℕ}

/-- Every full modular power arc orders the composed intervals of words. -/
theorem wordInterval_ordered (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (v t : List A.Letter) (hv : v.length = L) (ht : t.length = L)
    (harc : PowerArc k (b ^ L) (A.encode v) (A.encode t)) :
    (A.wordInterval v).left + (A.wordInterval v).width ≤ (A.wordInterval t).left := by
  have hX : A.encode v < b ^ L := by simpa only [hv] using A.encode_lt v
  have hY : A.encode t < b ^ L := by simpa only [ht] using A.encode_lt t
  obtain ⟨j, hj, hlow, hfirst⟩ := powerArc_least_digit k n b L _ _ hk hb hbase hL hX hY harc
  exact A.wordInterval_ordered_at (by omega) v t j (hv.trans ht.symm) (by omega) hlow hfirst

/-- The word chosen from an image membership; equal lengths will prove uniqueness. -/
noncomputable def decode (A : IntervalAlphabet k b) (E : Finset (List A.Letter))
    (x : ℕ) (hx : x ∈ E.image A.encode) : List A.Letter :=
  Classical.choose (Finset.mem_image.mp hx)

theorem decode_mem (A : IntervalAlphabet k b) (E : Finset (List A.Letter))
    (x : ℕ) (hx : x ∈ E.image A.encode) : A.decode E x hx ∈ E :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).1

theorem encode_decode (A : IntervalAlphabet k b) (E : Finset (List A.Letter))
    (x : ℕ) (hx : x ∈ E.image A.encode) : A.encode (A.decode E x hx) = x :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).2

/-- Any selected set of length-L words forms an interval alphabet modulo b^L. -/
noncomputable def wordAlphabet (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (E : Finset (List A.Letter)) (hlen : ∀ v ∈ E, v.length = L) :
    IntervalAlphabet k (b ^ L) where
  support := E.image A.encode
  residue_lt x hx := by
    rw [← A.encode_decode E x hx]
    simpa only [hlen _ (A.decode_mem E x hx)] using A.encode_lt (A.decode E x hx)
  interval x hx := A.wordInterval (A.decode E x hx)
  ordered x hx y hy harc := by
    apply A.wordInterval_ordered n L hk hb hbase hL
      (A.decode E x hx) (A.decode E y hy)
      (hlen _ (A.decode_mem E x hx)) (hlen _ (A.decode_mem E y hy))
    simpa only [A.encode_decode] using harc

/-- Passing to encoded residues preserves the number of selected words. -/
theorem wordAlphabet_card (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (E : Finset (List A.Letter)) (hlen : ∀ v ∈ E, v.length = L) :
    (A.wordAlphabet n L hk hb hbase hL E hlen).support.card = E.card := by
  apply Finset.card_image_iff.mpr
  intro v hv t ht heq
  exact A.encode_injective_equal_length (by omega) v t ((hlen v hv).trans (hlen t ht).symm) heq

/-- The arbitrary image representative really is the original selected word. -/
theorem wordAlphabet_interval_eq (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (E : Finset (List A.Letter)) (hlen : ∀ v ∈ E, v.length = L)
    (x : ℕ) (hx : x ∈ (A.wordAlphabet n L hk hb hbase hL E hlen).support)
    (v : List A.Letter) (hv : v ∈ E) (hcode : A.encode v = x) :
    (A.wordAlphabet n L hk hb hbase hL E hlen).interval x hx = A.wordInterval v := by
  change A.wordInterval (A.decode E x hx) = A.wordInterval v
  congr 1
  exact A.encode_injective_equal_length (by omega) _ _
    ((hlen _ (A.decode_mem E x hx)).trans (hlen v hv).symm)
    ((A.encode_decode E x hx).trans hcode.symm)

/-- A common lower bound on actual word products survives encoding unchanged. -/
theorem wordAlphabet_min_width (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (E : Finset (List A.Letter)) (hlen : ∀ v ∈ E, v.length = L)
    (ε : ℝ)
    (hwidth : ∀ v ∈ E, ε ≤ StoppingWords.width (fun a => (A.letterInterval a).width) v) :
    ∀ x (hx : x ∈ (A.wordAlphabet n L hk hb hbase hL E hlen).support),
      ε ≤ ((A.wordAlphabet n L hk hb hbase hL E hlen).interval x hx).width := by
  intro x hx
  change ε ≤ (A.wordInterval (A.decode E x hx)).width
  rw [A.wordInterval_width]
  exact hwidth _ (A.decode_mem E x hx)

/-- Encoding and affine composition preserve the selected word moment exactly. -/
theorem wordAlphabet_moment (A : IntervalAlphabet k b) (n L : ℕ)
    (hk : 1 ≤ k) (hb : 2 ≤ b) (hbase : b = n ^ k) (hL : 1 ≤ L)
    (E : Finset (List A.Letter)) (hlen : ∀ v ∈ E, v.length = L) (f : ℝ) :
    (A.wordAlphabet n L hk hb hbase hL E hlen).moment f =
      StoppingWords.moment (fun a => (A.letterInterval a).width) f E := by
  classical
  symm
  unfold StoppingWords.moment IntervalAlphabet.moment
  refine Finset.sum_bij
    (fun v hv => (⟨A.encode v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩ :
      ↥(A.wordAlphabet n L hk hb hbase hL E hlen).support)) ?_ ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_attach _ _
  · intro v hv t ht heq
    exact A.encode_injective_equal_length (by omega) v t
      ((hlen v hv).trans (hlen t ht).symm) (congrArg Subtype.val heq)
  · intro x _
    obtain ⟨v, hv, hcode⟩ := Finset.mem_image.mp x.property
    exact ⟨v, hv, Subtype.ext hcode⟩
  · intro v hv
    rw [A.wordAlphabet_interval_eq n L hk hb hbase hL E hlen
      (A.encode v) _ v hv rfl, A.wordInterval_width]

end IntervalAlphabet
end NK
