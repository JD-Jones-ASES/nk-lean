import NK.Intervals

/-! Ordinary finite directed-graph interval alphabets and actual nesting.
No optimization or product identity is part of the definitions. -/
namespace NK

universe u v

/-- Selected vertices carry positive intervals; absent vertices carry none. -/
structure DigraphAlphabet {V : Type u} (G : V → V → Prop) where
  interval : V → Option UnitInterval
  ordered : ∀ x y I J, interval x = some I → interval y = some J → G x y →
    I.left + I.width ≤ J.left

namespace DigraphAlphabet

variable {V : Type u} {W : Type v} {G : V → V → Prop} {H : W → W → Prop}

noncomputable def weight (f : ℝ) : Option UnitInterval → ℝ
  | none => 0
  | some I => I.width ^ f

noncomputable def moment [Fintype V] (A : DigraphAlphabet G) (f : ℝ) : ℝ :=
  ∑ x, weight f (A.interval x)

def empty (G : V → V → Prop) : DigraphAlphabet G where
  interval _ := none
  ordered := by intros; contradiction

@[simp] theorem empty_moment [Fintype V] (f : ℝ) : (empty G).moment f = 0 := by
  simp [moment, empty, weight]

theorem weight_nonneg (f : ℝ) (I : Option UnitInterval) : 0 ≤ weight f I := by
  cases I with
  | none => exact le_rfl
  | some I => exact Real.rpow_nonneg I.width_pos.le f

theorem moment_nonneg [Fintype V] (A : DigraphAlphabet G) (f : ℝ) : 0 ≤ A.moment f :=
  Finset.sum_nonneg (fun x _ => weight_nonneg f (A.interval x))

theorem weight_le_one (f : ℝ) (hf : 0 ≤ f) (I : Option UnitInterval) : weight f I ≤ 1 := by
  cases I with
  | none => norm_num [weight]
  | some I =>
    simpa only [weight, Real.one_rpow] using Real.rpow_le_rpow I.width_pos.le I.width_le_one hf

theorem moment_le_card [Fintype V] (A : DigraphAlphabet G) (f : ℝ) (hf : 0 ≤ f) :
    A.moment f ≤ (Fintype.card V : ℝ) := by
  calc
    _ ≤ ∑ _x : V, (1 : ℝ) := Finset.sum_le_sum (fun x _ => weight_le_one f hf (A.interval x))
    _ = _ := by simp

/-- The ordinary directed lexicographic product, including any input loops. -/
def lex (G : V → V → Prop) (H : W → W → Prop) (p q : V × W) : Prop :=
  G p.1 q.1 ∨ (p.1 = q.1 ∧ H p.2 q.2)

noncomputable def optionComp (a b : Option UnitInterval) : Option UnitInterval :=
  a.bind fun I => b.map I.comp

theorem optionComp_eq_some (a b : Option UnitInterval) (K : UnitInterval) :
    optionComp a b = some K ↔ ∃ I J, a = some I ∧ b = some J ∧ I.comp J = K := by
  cases a <;> cases b <;> simp [optionComp]

noncomputable def product (A : DigraphAlphabet G) (B : DigraphAlphabet H) :
    DigraphAlphabet (lex G H) where
  interval p := optionComp (A.interval p.1) (B.interval p.2)
  ordered := by
    rintro ⟨x,u⟩ ⟨y,v⟩ I J hI hJ hArc
    obtain ⟨P,U,hP,hU,rfl⟩ := (optionComp_eq_some _ _ _).mp hI
    obtain ⟨Q,V,hQ,hV,rfl⟩ := (optionComp_eq_some _ _ _).mp hJ
    rcases hArc with hxy | ⟨rfl, huv⟩
    · exact UnitInterval.separated_comp P Q U V (A.ordered x y P Q hP hQ hxy)
    · have hPQ : P = Q := Option.some.inj (hP.symm.trans hQ)
      subst Q
      exact UnitInterval.comp_separated P U V (B.ordered u v U V hU hV huv)

theorem weight_comp (f : ℝ) (a b : Option UnitInterval) :
    weight f (optionComp a b) = weight f a * weight f b := by
  cases a with
  | none => simp [optionComp, weight]
  | some A =>
    cases b with
    | none => simp [optionComp, weight]
    | some B =>
      simpa only [optionComp, Option.bind_some, Option.map_some, weight, UnitInterval.comp_width]
        using Real.mul_rpow A.width_pos.le B.width_pos.le

/-- The nested construction has exactly the product moment. -/
theorem product_moment [Fintype V] [Fintype W] (A : DigraphAlphabet G) (B : DigraphAlphabet H)
    (f : ℝ) : (product A B).moment f = A.moment f * B.moment f := by
  simp only [moment, product, Fintype.sum_prod_type, weight_comp, ← Finset.mul_sum, ← Finset.sum_mul]

end DigraphAlphabet
namespace UnitInterval

/-- Place a contained interval in its parent's unit coordinates. -/
noncomputable def normalize (P I : UnitInterval) (hl : P.left ≤ I.left)
    (hr : I.left + I.width ≤ P.left + P.width) : UnitInterval where
  left := (I.left - P.left) / P.width
  width := I.width / P.width
  left_nonneg := div_nonneg (sub_nonneg.mpr hl) P.width_pos.le
  width_pos := div_pos I.width_pos P.width_pos
  right_le_one := by
    rw [← add_div]
    apply (div_le_one P.width_pos).mpr
    linarith

@[simp] theorem normalize_width (P I : UnitInterval) (hl hr) :
    (normalize P I hl hr).width = I.width / P.width := rfl

theorem normalize_ordered (P I J : UnitInterval) (hlI hrI hlJ hrJ)
    (h : I.left + I.width ≤ J.left) :
    (normalize P I hlI hrI).left + (normalize P I hlI hrI).width ≤
      (normalize P J hlJ hrJ).left := by
  change (I.left-P.left)/P.width + I.width/P.width ≤ (J.left-P.left)/P.width
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right P.width_pos).mpr
  linarith

end UnitInterval

namespace IntervalHull

variable {V : Type u} [Fintype V]

def occupied (a : V → Option UnitInterval) : Prop := ∃ x I, a x = some I

def leftValue : Option UnitInterval → ℝ
  | none => 1
  | some I => I.left

def rightValue : Option UnitInterval → ℝ
  | none => 0
  | some I => I.left + I.width

noncomputable def lefts (a : V → Option UnitInterval) : Finset ℝ := by
  classical
  exact insert 1 (Finset.univ.image (fun x => leftValue (a x)))

noncomputable def rights (a : V → Option UnitInterval) : Finset ℝ := by
  classical
  exact insert 0 (Finset.univ.image (fun x => rightValue (a x)))

theorem lefts_nonempty (a : V → Option UnitInterval) : (lefts a).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

theorem rights_nonempty (a : V → Option UnitInterval) : (rights a).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

noncomputable def left (a : V → Option UnitInterval) : ℝ := (lefts a).min' (lefts_nonempty a)
noncomputable def right (a : V → Option UnitInterval) : ℝ := (rights a).max' (rights_nonempty a)

theorem left_nonneg (a : V → Option UnitInterval) : 0 ≤ left a := by
  classical
  apply Finset.le_min'
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    cases h : a x with
    | none => norm_num [leftValue]
    | some I => exact I.left_nonneg

theorem right_le_one (a : V → Option UnitInterval) : right a ≤ 1 := by
  classical
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · norm_num
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    cases h : a x with
    | none => norm_num [rightValue]
    | some I => exact I.right_le_one

theorem left_le (a : V → Option UnitInterval) (x : V) (I : UnitInterval) (h : a x = some I) :
    left a ≤ I.left := by
  classical
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by rw [h]; rfl⟩

theorem le_right (a : V → Option UnitInterval) (x : V) (I : UnitInterval) (h : a x = some I) :
    I.left + I.width ≤ right a := by
  classical
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by rw [h]; rfl⟩

theorem left_lt_right (a : V → Option UnitInterval) (ha : occupied a) : left a < right a := by
  obtain ⟨x,I,hI⟩ := ha
  have hL := left_le a x I hI
  have hR := le_right a x I hI
  linarith [I.width_pos]

noncomputable def hull (a : V → Option UnitInterval) (ha : occupied a) : UnitInterval where
  left := left a
  width := right a - left a
  left_nonneg := left_nonneg a
  width_pos := sub_pos.mpr (left_lt_right a ha)
  right_le_one := by linarith [right_le_one a]

theorem hull_contains (a : V → Option UnitInterval) (ha : occupied a)
    (x : V) (I : UnitInterval) (hx : a x = some I) :
    (hull a ha).left ≤ I.left ∧ I.left + I.width ≤ (hull a ha).left + (hull a ha).width := by
  constructor
  · exact left_le a x I hx
  · dsimp [hull]
    linarith [le_right a x I hx]

/-- Ordering every constituent interval orders the actual hull endpoints. -/
theorem right_le_left (a b : V → Option UnitInterval)
    (h : ∀ x y I J, a x = some I → b y = some J → I.left + I.width ≤ J.left) :
    right a ≤ left b := by
  classical
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact left_nonneg b
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    cases hx : a x with
    | none => exact left_nonneg b
    | some I =>
      change I.left + I.width ≤ left b
      apply Finset.le_min'
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact I.right_le_one
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ht
        cases hy : b y with
        | none => exact I.right_le_one
        | some J => exact h x y I J hx hy

end IntervalHull

namespace DigraphAlphabet

variable {V : Type u} {G : V → V → Prop}

noncomputable def normalizeOption (P : UnitInterval) :
    (a : Option UnitInterval) →
    (∀ I, a = some I → P.left ≤ I.left ∧ I.left + I.width ≤ P.left + P.width) →
    Option UnitInterval
  | none, _ => none
  | some I, hc => some (UnitInterval.normalize P I (hc I rfl).1 (hc I rfl).2)

theorem normalizeOption_none_of_eq (P : UnitInterval) (a : Option UnitInterval) (hc)
    (ha : a = none) : normalizeOption P a hc = none := by subst a; rfl

theorem normalizeOption_some_of_eq (P : UnitInterval) (a : Option UnitInterval) (hc)
    (I : UnitInterval) (ha : a = some I) :
    normalizeOption P a hc = some (UnitInterval.normalize P I (hc I ha).1 (hc I ha).2) := by
  subst a
  rfl

noncomputable def normalize (A : DigraphAlphabet G) (P : UnitInterval)
    (hc : ∀ x I, A.interval x = some I → P.left ≤ I.left ∧ I.left + I.width ≤ P.left + P.width) :
    DigraphAlphabet G where
  interval x := normalizeOption P (A.interval x) (hc x)
  ordered := by
    intro x y I J hI hJ hxy
    cases hx : A.interval x with
    | none =>
      rw [normalizeOption_none_of_eq P _ _ hx] at hI
      contradiction
    | some X =>
      cases hy : A.interval y with
      | none =>
        rw [normalizeOption_none_of_eq P _ _ hy] at hJ
        contradiction
      | some Y =>
        have hi : UnitInterval.normalize P X (hc x X hx).1 (hc x X hx).2 = I := by
          rw [normalizeOption_some_of_eq P _ _ X hx] at hI
          exact Option.some.inj hI
        have hj : UnitInterval.normalize P Y (hc y Y hy).1 (hc y Y hy).2 = J := by
          rw [normalizeOption_some_of_eq P _ _ Y hy] at hJ
          exact Option.some.inj hJ
        rw [← hi, ← hj]
        exact UnitInterval.normalize_ordered P X Y _ _ _ _ (A.ordered x y X Y hx hy hxy)

/-- Rescaling into a containing interval has an exact moment factor. -/
theorem normalize_moment [Fintype V] (A : DigraphAlphabet G) (P : UnitInterval)
    (hc : ∀ x I, A.interval x = some I → P.left ≤ I.left ∧ I.left + I.width ≤ P.left + P.width)
    (f : ℝ) : A.moment f = P.width ^ f * (normalize A P hc).moment f := by
  unfold moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change weight f (A.interval x) = P.width ^ f * weight f (normalizeOption P (A.interval x) (hc x))
  obtain hx | ⟨I,hx⟩ := (A.interval x).eq_none_or_eq_some
  · rw [normalizeOption_none_of_eq P _ _ hx, hx]
    simp only [weight, mul_zero]
  · rw [normalizeOption_some_of_eq P _ _ I hx, hx]
    simp only [weight, UnitInterval.normalize_width]
    rw [← Real.mul_rpow P.width_pos.le (div_nonneg I.width_pos.le P.width_pos.le)]
    congr 1
    field_simp [P.width_pos.ne']

end DigraphAlphabet

end NK
