import NK.WordIntervals

/-! # Exact transformations of ordered interval alphabets

Translation copies intervals; residue reflection reverses the order of arcs and
reflects the intervals; affine placement rescales every width by the same factor.
All constructions use the full modular power relation, for arbitrary k.
-/
namespace NK
namespace UnitInterval

/-- Reflection in the midpoint of the unit interval, preserving width. -/
noncomputable def reflect (I : UnitInterval) : UnitInterval where
  left := 1 - (I.left + I.width)
  width := I.width
  left_nonneg := by linarith [I.right_le_one]
  width_pos := I.width_pos
  right_le_one := by linarith [I.left_nonneg]

@[simp] theorem reflect_left (I : UnitInterval) :
    I.reflect.left = 1 - (I.left + I.width) := rfl
@[simp] theorem reflect_width (I : UnitInterval) : I.reflect.width = I.width := rfl

theorem reflect_separated (I J : UnitInterval) (h : J.left + J.width ≤ I.left) :
    I.reflect.left + I.reflect.width ≤ J.reflect.left := by
  simp only [reflect_left, reflect_width]
  linarith

end UnitInterval
namespace IntervalAlphabet

variable {k M : ℕ}

/-- Shared finite-image construction, with a proved injective residue label map. -/
noncomputable def relabel (A : IntervalAlphabet k M) (code : A.Letter → ℕ)
    (_hcode : Function.Injective code) (hbound : ∀ a, code a < M)
    (J : A.Letter → UnitInterval)
    (horder : ∀ a c, PowerArc k M (code a) (code c) → (J a).left + (J a).width ≤ (J c).left) :
    IntervalAlphabet k M where
  support := Finset.univ.image code
  residue_lt x hx := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact hbound a
  interval x hx := J (Classical.choose (Finset.mem_image.mp hx))
  ordered x hx y hy harc := by
    apply horder
    simpa only [(Classical.choose_spec (Finset.mem_image.mp hx)).2,
      (Classical.choose_spec (Finset.mem_image.mp hy)).2] using harc

/-- Relabelling preserves the original number of residues. -/
theorem relabel_card (A : IntervalAlphabet k M) (code : A.Letter → ℕ)
    (hcode : Function.Injective code) (hbound : ∀ a, code a < M)
    (J : A.Letter → UnitInterval)
    (horder : ∀ a c, PowerArc k M (code a) (code c) → (J a).left + (J a).width ≤ (J c).left) :
    (A.relabel code hcode hbound J horder).support.card = A.support.card := by
  change (Finset.univ.image code).card = _
  rw [Finset.card_image_of_injective _ hcode, Finset.card_univ, Fintype.card_coe]

/-- The chosen image representative carries the prescribed interval. -/
theorem relabel_interval (A : IntervalAlphabet k M) (code : A.Letter → ℕ)
    (hcode : Function.Injective code) (hbound : ∀ a, code a < M)
    (J : A.Letter → UnitInterval)
    (horder : ∀ a c, PowerArc k M (code a) (code c) → (J a).left + (J a).width ≤ (J c).left)
    (a : A.Letter) (ha : code a ∈ (A.relabel code hcode hbound J horder).support) :
    (A.relabel code hcode hbound J horder).interval (code a) ha = J a := by
  change J (Classical.choose (Finset.mem_image.mp ha)) = J a
  apply congrArg J
  exact hcode (Classical.choose_spec (Finset.mem_image.mp ha)).2

/-- The moment of a finite-image alphabet is the sum of its prescribed widths. -/
theorem relabel_moment (A : IntervalAlphabet k M) (code : A.Letter → ℕ)
    (hcode : Function.Injective code) (hbound : ∀ a, code a < M)
    (J : A.Letter → UnitInterval)
    (horder : ∀ a c, PowerArc k M (code a) (code c) → (J a).left + (J a).width ≤ (J c).left)
    (f : ℝ) : (A.relabel code hcode hbound J horder).moment f = ∑ a, (J a).width ^ f := by
  classical
  symm
  unfold IntervalAlphabet.moment
  refine Finset.sum_bij
    (fun a _ => (⟨code a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩ :
      ↥(A.relabel code hcode hbound J horder).support)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_attach _ _
  · intro a ha c hc heq
    exact hcode (congrArg Subtype.val heq)
  · intro x _
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp x.property
    exact ⟨a, ha, Subtype.ext heq⟩
  · intro a ha
    rw [A.relabel_interval code hcode hbound J horder a _]

/-- Affine placement of every interval, on exactly the original support. -/
noncomputable def affine (A : IntervalAlphabet k M) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (htu : t + u ≤ 1) : IntervalAlphabet k M where
  support := A.support
  residue_lt := A.residue_lt
  interval x hx := (UnitInterval.mk t u ht hu htu).comp (A.interval x hx)
  ordered x hx y hy harc := UnitInterval.comp_separated _ _ _ (A.ordered x hx y hy harc)

@[simp] theorem affine_card (A : IntervalAlphabet k M) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (htu : t + u ≤ 1) :
    (A.affine t u ht hu htu).support.card = A.support.card := rfl

@[simp] theorem affine_left (A : IntervalAlphabet k M) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (htu : t + u ≤ 1) (x : ℕ) (hx : x ∈ A.support) :
    ((A.affine t u ht hu htu).interval x hx).left = t + u * (A.interval x hx).left := rfl

@[simp] theorem affine_width (A : IntervalAlphabet k M) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (htu : t + u ≤ 1) (x : ℕ) (hx : x ∈ A.support) :
    ((A.affine t u ht hu htu).interval x hx).width = u * (A.interval x hx).width := rfl

/-- Affine placement scales the exact moment by u^f. -/
theorem affine_moment (A : IntervalAlphabet k M) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (htu : t + u ≤ 1) (f : ℝ) :
    (A.affine t u ht hu htu).moment f = u ^ f * A.moment f := by
  unfold IntervalAlphabet.moment
  change (∑ a ∈ A.support.attach, (u * (A.interval a.val a.property).width) ^ f) = _
  simp_rw [Real.mul_rpow hu.le (A.interval _ _).width_pos.le]
  rw [Finset.mul_sum]

end IntervalAlphabet
namespace AlphabetSymmetries

/-- Bounded residues can be recovered from their translated residues. -/
theorem translate_injective (M t x y : ℕ) (hx : x < M) (hy : y < M)
    (h : (x+t) % M = (y+t) % M) : x = y :=
  (Nat.ModEq.add_right_cancel' t h).eq_of_lt_of_lt hx hy

/-- Translation preserves the full power relation in both directions. -/
theorem translate_arc_iff (k M t x y : ℕ) (hx : x < M) (hy : y < M) :
    PowerArc k M ((x+t) % M) ((y+t) % M) ↔ PowerArc k M x y := by
  constructor
  · rintro ⟨hne, z, hz⟩
    refine ⟨fun h => hne (by rw [h]), z, ?_⟩
    rw [Nat.mod_add_mod, Nat.mod_mod] at hz
    have heq : x+t+z^k = x+z^k+t := by omega
    rw [heq] at hz
    exact Nat.ModEq.add_right_cancel' t hz
  · rintro ⟨hne, z, hz⟩
    refine ⟨fun h => hne (translate_injective M t x y hx hy h), z, ?_⟩
    rw [Nat.mod_add_mod, Nat.mod_mod]
    have h := Nat.ModEq.add_right t hz
    have heq : x+t+z^k = x+z^k+t := by omega
    rwa [heq]

/-- Negation of a bounded natural residue. -/
def reflectResidue (M x : ℕ) : ℕ := (M-x) % M

theorem add_reflectResidue_mod (M x : ℕ) (hx : x < M) :
    (x + reflectResidue M x) % M = 0 := by
  unfold reflectResidue
  rw [Nat.add_mod_mod]
  have h : x + (M-x) = M := by omega
  rw [h, Nat.mod_self]

theorem reflect_injective (M x y : ℕ) (hx : x < M) (hy : y < M)
    (h : reflectResidue M x = reflectResidue M y) : x = y := by
  have heq : Nat.ModEq M (x + reflectResidue M x) (y + reflectResidue M x) := by
    exact (add_reflectResidue_mod M x hx).trans (by rw [h]; exact (add_reflectResidue_mod M y hy).symm)
  exact (Nat.ModEq.add_right_cancel' (reflectResidue M x) heq).eq_of_lt_of_lt hx hy

theorem reflect_involutive (M x : ℕ) (hx : x < M) :
    reflectResidue M (reflectResidue M x) = x := by
  by_cases hzero : x = 0
  · simp [reflectResidue, hzero]
  · have hsub : M-x < M := by omega
    unfold reflectResidue
    rw [Nat.mod_eq_of_lt hsub]
    have h : M - (M-x) = x := by omega
    rw [h, Nat.mod_eq_of_lt hx]

/-- Reflection reverses the ordered full power relation for every exponent k. -/
theorem reflect_arc_reverse (k M x y : ℕ) (hx : x < M) (hy : y < M)
    (harc : PowerArc k M (reflectResidue M x) (reflectResidue M y)) : PowerArc k M y x := by
  obtain ⟨hne, z, hz⟩ := harc
  refine ⟨fun h => hne (by rw [h]), z, ?_⟩
  have h := Nat.ModEq.add_right (x+y) hz
  have hnx : Nat.ModEq M (x + reflectResidue M x) 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using add_reflectResidue_mod M x hx
  have hny : Nat.ModEq M (y + reflectResidue M y) 0 := by
    simpa only [Nat.ModEq, Nat.zero_mod] using add_reflectResidue_mod M y hy
  have hleft : Nat.ModEq M (x + reflectResidue M x + (y+z^k)) (y+z^k) := by
    simpa only [Nat.zero_add] using Nat.ModEq.add_right (y+z^k) hnx
  have hright : Nat.ModEq M (y + reflectResidue M y + x) x := by
    simpa only [Nat.zero_add] using Nat.ModEq.add_right x hny
  have heq1 : reflectResidue M x + z^k + (x+y) = x + reflectResidue M x + (y+z^k) := by omega
  have heq2 : reflectResidue M y + (x+y) = y + reflectResidue M y + x := by omega
  rw [heq1, heq2] at h
  exact hleft.symm.trans (h.trans hright)

/-- Translation by one exchanges the two parity classes at every even modulus. -/
theorem translate_one_parity (M x : ℕ) (hM : 2 ∣ M) :
    ((x+1) % M) % 2 = (x % 2 + 1) % 2 := by
  rw [Nat.mod_mod_of_dvd _ hM, Nat.add_mod]

theorem translate_one_parity_ne (M x : ℕ) (hM : 2 ∣ M) :
    ((x+1) % M) % 2 ≠ x % 2 := by
  rw [translate_one_parity M x hM]
  omega

/-- Residue reflection preserves parity at an even modulus. -/
theorem reflect_parity (M x : ℕ) (hM : 2 ∣ M) (hx : x < M) :
    ((M-x) % M) % 2 = x % 2 := by
  have h := congrArg (fun a : ℕ => a % 2) (add_reflectResidue_mod M x hx)
  rw [Nat.mod_mod_of_dvd _ hM] at h
  change (x + ((M-x) % M)) % 2 = 0 at h
  omega

end AlphabetSymmetries
namespace IntervalAlphabet

variable {k M : ℕ}

/-- Cyclic translation of residues, copying the original intervals. -/
noncomputable def translate (A : IntervalAlphabet k M) (t : ℕ) : IntervalAlphabet k M :=
  A.relabel (fun a => (a.val+t) % M)
    (fun a c h => Subtype.ext (AlphabetSymmetries.translate_injective M t a.val c.val
      (A.residue_lt _ a.property) (A.residue_lt _ c.property) h))
    (fun a => Nat.mod_lt _ (by have h := A.residue_lt _ a.property; omega))
    A.letterInterval
    (fun a c h => A.ordered a.val a.property c.val c.property
      ((AlphabetSymmetries.translate_arc_iff k M t a.val c.val
        (A.residue_lt _ a.property) (A.residue_lt _ c.property)).mp h))

/-- Reflection of residues and intervals, reversing both orders. -/
noncomputable def reflect (A : IntervalAlphabet k M) : IntervalAlphabet k M :=
  A.relabel (fun a => AlphabetSymmetries.reflectResidue M a.val)
    (fun a c h => Subtype.ext (AlphabetSymmetries.reflect_injective M a.val c.val
      (A.residue_lt _ a.property) (A.residue_lt _ c.property) h))
    (fun a => Nat.mod_lt _ (by have h := A.residue_lt _ a.property; omega))
    (fun a => (A.letterInterval a).reflect)
    (fun a c h => UnitInterval.reflect_separated _ _
      (A.ordered c.val c.property a.val a.property
        (AlphabetSymmetries.reflect_arc_reverse k M a.val c.val
          (A.residue_lt _ a.property) (A.residue_lt _ c.property) h)))

theorem mem_translate_support (A : IntervalAlphabet k M) (t x : ℕ) :
    x ∈ (A.translate t).support ↔ ∃ a : A.Letter, (a.val+t) % M = x := by
  change x ∈ Finset.univ.image (fun a : A.Letter => (a.val+t) % M) ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_reflect_support (A : IntervalAlphabet k M) (x : ℕ) :
    x ∈ A.reflect.support ↔ ∃ a : A.Letter, (M-a.val) % M = x := by
  change x ∈ Finset.univ.image (fun a : A.Letter => (M-a.val) % M) ↔ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem translate_interval (A : IntervalAlphabet k M) (t : ℕ) (a : A.Letter)
    (ha : (a.val+t) % M ∈ (A.translate t).support) :
    (A.translate t).interval ((a.val+t) % M) ha = A.letterInterval a :=
  A.relabel_interval _ _ _ _ _ a ha

theorem reflect_interval (A : IntervalAlphabet k M) (a : A.Letter)
    (ha : (M-a.val) % M ∈ A.reflect.support) :
    A.reflect.interval ((M-a.val) % M) ha = (A.letterInterval a).reflect :=
  A.relabel_interval _ _ _ _ _ a ha

@[simp] theorem translate_card (A : IntervalAlphabet k M) (t : ℕ) :
    (A.translate t).support.card = A.support.card := A.relabel_card _ _ _ _ _

@[simp] theorem reflect_card (A : IntervalAlphabet k M) :
    A.reflect.support.card = A.support.card := A.relabel_card _ _ _ _ _

@[simp] theorem translate_moment (A : IntervalAlphabet k M) (t : ℕ) (f : ℝ) :
    (A.translate t).moment f = A.moment f := by
  calc
    _ = ∑ a : A.Letter, (A.letterInterval a).width ^ f := A.relabel_moment _ _ _ _ _ f
    _ = _ := by simp only [letterInterval, IntervalAlphabet.moment, Finset.attach_eq_univ]

@[simp] theorem reflect_moment (A : IntervalAlphabet k M) (f : ℝ) :
    A.reflect.moment f = A.moment f := by
  calc
    _ = ∑ a : A.Letter, (A.letterInterval a).reflect.width ^ f := A.relabel_moment _ _ _ _ _ f
    _ = _ := by simp only [UnitInterval.reflect_width, letterInterval, IntervalAlphabet.moment, Finset.attach_eq_univ]

/-- The empty alphabet, available at every modulus. -/
def empty (k M : ℕ) : IntervalAlphabet k M where
  support := ∅
  residue_lt x hx := by simp at hx
  interval x hx := False.elim (by simp at hx)
  ordered x hx := by simp at hx

@[simp] theorem empty_moment (k M : ℕ) (f : ℝ) : (empty k M).moment f = 0 := by
  simp [moment, empty]

/-- A single residue carrying any unit interval; there is no nontrivial self-arc. -/
def singleton (k M x : ℕ) (hx : x < M) (I : UnitInterval) : IntervalAlphabet k M where
  support := {x}
  residue_lt y hy := by simpa only [Finset.mem_singleton.mp hy] using hx
  interval _ _ := I
  ordered y hy z hz harc := by
    have hyx := Finset.mem_singleton.mp hy
    have hzx := Finset.mem_singleton.mp hz
    exact False.elim (harc.1 (hyx.trans hzx.symm))

@[simp] theorem singleton_card (k M x : ℕ) (hx : x < M) (I : UnitInterval) :
    (singleton k M x hx I).support.card = 1 := by simp [singleton]

@[simp] theorem singleton_moment (k M x : ℕ) (hx : x < M) (I : UnitInterval) (f : ℝ) :
    (singleton k M x hx I).moment f = I.width ^ f := by
  simp [moment, singleton]

end IntervalAlphabet
end NK
