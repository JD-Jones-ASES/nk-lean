import NK.BinaryArc

/-! # Concrete four-branch interval gluing

Each child is already placed in the unit interval. The parent copies those
intervals onto disjoint residue labels `r+4*u`. Window inequalities are required
only for classes represented by actual child points, so empty children and
unoccupied parity classes are permitted.
-/
namespace NK.BinaryGlue

variable {m : ℕ}

/-- A labelled point of one of the four children. -/
abbrev Point (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) :=
  (r : Fin 4) × {u : ℕ // u ∈ (A r).support}

/-- The parent residue represented by a labelled child point. -/
def encode (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (p : Point A) : ℕ :=
  p.1.val + 4 * p.2.val

/-- Intervals are copied exactly from the already-placed children. -/
noncomputable def pointInterval (A : Fin 4 → IntervalAlphabet 2 (4 ^ m))
    (p : Point A) : UnitInterval := (A p.1).interval p.2.val p.2.property

/-- Numerical residue class modulo8, encoded by the label and tail parity. -/
def parityClass (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (p : Point A) : Fin 8 :=
  ⟨p.1.val + 4 * (p.2.val % 2), by
    have hr := p.1.isLt
    have hu : p.2.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega⟩

theorem parityClass_eq_mod (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (p : Point A) :
    (parityClass A p).val = encode A p % 8 :=
  (BinaryArc.branch_mod_eight p.1.val p.2.val p.1.isLt).symm

theorem encode_lt (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (p : Point A) :
    encode A p < 4 ^ (m+1) := by
  rw [pow_succ, mul_comm]
  exact BinaryArc.branch_lt _ _ _ p.1.isLt ((A p.1).residue_lt _ p.2.property)

/-- Distinct labels or distinct tail residues give distinct parent residues. -/
theorem encode_injective (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) :
    Function.Injective (encode A) := by
  rintro ⟨r, u⟩ ⟨s, v⟩ heq
  have hrs : r = s := by
    apply Fin.ext
    have h := congrArg (fun x : ℕ => x % 4) heq
    simpa only [encode, BinaryArc.branch_mod_four _ _ r.isLt,
      BinaryArc.branch_mod_four _ _ s.isLt] using h
  subst s
  have huv : u = v := by
    apply Subtype.ext
    dsimp [encode] at heq
    omega
  subst v
  rfl

/-- Union of the four residue-labelled child supports. -/
def support (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) : Finset ℕ :=
  Finset.univ.image (encode A)

theorem mem_support (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (x : ℕ) :
    x ∈ support A ↔ ∃ r : Fin 4, ∃ u ∈ (A r).support, r.val + 4*u = x := by
  constructor
  · intro hx
    obtain ⟨⟨r, u⟩, _, h⟩ := Finset.mem_image.mp hx
    exact ⟨r, u.val, u.property, h⟩
  · rintro ⟨r, u, hu, h⟩
    exact Finset.mem_image.mpr ⟨⟨r, ⟨u, hu⟩⟩, Finset.mem_univ _, h⟩

noncomputable def decode (A : Fin 4 → IntervalAlphabet 2 (4 ^ m))
    (x : ℕ) (hx : x ∈ support A) : Point A :=
  Classical.choose (Finset.mem_image.mp hx)

theorem encode_decode (A : Fin 4 → IntervalAlphabet 2 (4 ^ m))
    (x : ℕ) (hx : x ∈ support A) : encode A (decode A x hx) = x :=
  (Classical.choose_spec (Finset.mem_image.mp hx)).2

theorem decode_encode (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (p : Point A)
    (hp : encode A p ∈ support A) : decode A (encode A p) hp = p :=
  encode_injective A (encode_decode A _ hp)

/-- The only extra interval comparisons required beyond the child alphabets are
comparisons across adjacent occupied numerical classes modulo8. -/
theorem ordered_of_cross_order (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (hm : 1 ≤ m)
    (hcross : ∀ p q : Point A, ((parityClass A p).val + 1) % 8 = (parityClass A q).val →
      (pointInterval A p).left + (pointInterval A p).width ≤ (pointInterval A q).left)
    (p q : Point A) (harc : PowerArc 2 (4 ^ (m+1)) (encode A p) (encode A q)) :
    (pointInterval A p).left + (pointInterval A p).width ≤ (pointInterval A q).left := by
  rcases p with ⟨r, u⟩
  rcases q with ⟨s, v⟩
  have hrel := (BinaryArc.powerArc_fourBranch_iff m r.val s.val u.val v.val hm r.isLt s.isLt
    ((A r).residue_lt _ u.property) ((A s).residue_lt _ v.property)).mp harc
  rcases hrel with ⟨hrs, htail⟩ | hnext | hwrap
  · have heq : r = s := Fin.ext hrs
    subst s
    exact (A r).ordered u.val u.property v.val v.property htail
  · apply hcross ⟨r, u⟩ ⟨s, v⟩
    have h := (BinaryArc.branch_successor_iff r.val s.val u.val v.val r.isLt s.isLt).mpr (Or.inl hnext)
    rw [Nat.add_mod, BinaryArc.branch_mod_eight _ _ r.isLt,
      BinaryArc.branch_mod_eight _ _ s.isLt] at h
    exact h
  · apply hcross ⟨r, u⟩ ⟨s, v⟩
    have h := (BinaryArc.branch_successor_iff r.val s.val u.val v.val r.isLt s.isLt).mpr (Or.inr hwrap)
    rw [Nat.add_mod, BinaryArc.branch_mod_eight _ _ r.isLt,
      BinaryArc.branch_mod_eight _ _ s.isLt] at h
    exact h

/-- Concrete gluing from occupied parity-window containment and cycle ordering. -/
noncomputable def glue (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (hm : 1 ≤ m)
    (L R : Fin 8 → ℝ)
    (hinside : ∀ p : Point A, L (parityClass A p) ≤ (pointInterval A p).left ∧
      (pointInterval A p).left + (pointInterval A p).width ≤ R (parityClass A p))
    (hcycle : ∀ p q : Point A, ((parityClass A p).val + 1) % 8 = (parityClass A q).val →
      R (parityClass A p) ≤ L (parityClass A q)) : IntervalAlphabet 2 (4 ^ (m+1)) where
  support := support A
  residue_lt x hx := by rw [← encode_decode A x hx]; exact encode_lt A _
  interval x hx := pointInterval A (decode A x hx)
  ordered x hx y hy harc := by
    apply ordered_of_cross_order A hm
      (fun p q hpq => (hinside p).2.trans ((hcycle p q hpq).trans (hinside q).1))
      (decode A x hx) (decode A y hy)
    simpa only [encode_decode] using harc

/-- The interval at an encoded child point is exactly its original interval. -/
theorem glue_interval (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (hm : 1 ≤ m)
    (L R : Fin 8 → ℝ)
    (hinside : ∀ p : Point A, L (parityClass A p) ≤ (pointInterval A p).left ∧
      (pointInterval A p).left + (pointInterval A p).width ≤ R (parityClass A p))
    (hcycle : ∀ p q : Point A, ((parityClass A p).val + 1) % 8 = (parityClass A q).val →
      R (parityClass A p) ≤ L (parityClass A q))
    (p : Point A) (hp : encode A p ∈ (glue A hm L R hinside hcycle).support) :
    (glue A hm L R hinside hcycle).interval (encode A p) hp = pointInterval A p := by
  change pointInterval A (decode A (encode A p) hp) = pointInterval A p
  exact congrArg (pointInterval A) (decode_encode A p hp)

section Counting

variable (A : Fin 4 → IntervalAlphabet 2 (4 ^ m)) (hm : 1 ≤ m)
    (L R : Fin 8 → ℝ)
    (hinside : ∀ p : Point A, L (parityClass A p) ≤ (pointInterval A p).left ∧
      (pointInterval A p).left + (pointInterval A p).width ≤ R (parityClass A p))
    (hcycle : ∀ p q : Point A, ((parityClass A p).val + 1) % 8 = (parityClass A q).val →
      R (parityClass A p) ≤ L (parityClass A q))

/-- The labelled union has exactly the sum of the four child cardinalities. -/
theorem glue_card : (glue A hm L R hinside hcycle).support.card =
    ∑ r : Fin 4, (A r).support.card := by
  change (Finset.univ.image (encode A)).card = _
  rw [Finset.card_image_of_injective _ (encode_injective A), Finset.card_univ]
  change Fintype.card ((r : Fin 4) × {u : ℕ // u ∈ (A r).support}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]

/-- No width or moment is changed when a child point receives its parent label. -/
theorem glue_moment_eq_point_sum (f : ℝ) :
    (glue A hm L R hinside hcycle).moment f =
      ∑ p : Point A, (pointInterval A p).width ^ f := by
  classical
  symm
  unfold IntervalAlphabet.moment
  refine Finset.sum_bij
    (fun p _ => (⟨encode A p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩ :
      ↥(glue A hm L R hinside hcycle).support)) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_attach _ _
  · intro p hp q hq heq
    exact encode_injective A (congrArg Subtype.val heq)
  · intro x _
    obtain ⟨p, hp, hcode⟩ := Finset.mem_image.mp x.property
    exact ⟨p, hp, Subtype.ext hcode⟩
  · intro p hp
    rw [glue_interval A hm L R hinside hcycle p _]

/-- The full parent moment is the exact sum of its four child moments. -/
theorem glue_moment (f : ℝ) : (glue A hm L R hinside hcycle).moment f =
    ∑ r : Fin 4, (A r).moment f := by
  rw [glue_moment_eq_point_sum]
  rw [Fintype.sum_sigma]
  simp only [pointInterval, IntervalAlphabet.moment, Finset.attach_eq_univ]

end Counting
end NK.BinaryGlue
