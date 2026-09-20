import NK.Definitions

/-! Affine interval composition and the integer discretization used by the
interval transfer. The first list entry is the outermost affine map. -/
namespace NK
namespace UnitInterval

@[simp] theorem width_nonneg (I : UnitInterval) : 0 ≤ I.width := I.width_pos.le
@[simp] theorem width_le_one (I : UnitInterval) : I.width ≤ 1 := by
  linarith [I.right_le_one, I.left_nonneg]
@[simp] theorem left_lt_one (I : UnitInterval) : I.left < 1 := by
  linarith [I.right_le_one, I.width_pos]

def unit : UnitInterval := ⟨0, 1, le_rfl, zero_lt_one, by norm_num⟩

/-- Composition of the affine maps associated to two unit intervals. -/
noncomputable def comp (I J : UnitInterval) : UnitInterval where
  left := I.left + I.width * J.left
  width := I.width * J.width
  left_nonneg := add_nonneg I.left_nonneg (mul_nonneg I.width_nonneg J.left_nonneg)
  width_pos := mul_pos I.width_pos J.width_pos
  right_le_one := by
    have h := mul_le_mul_of_nonneg_left J.right_le_one I.width_nonneg
    nlinarith [I.right_le_one]

@[simp] theorem comp_width (I J : UnitInterval) : (I.comp J).width = I.width * J.width := rfl
@[simp] theorem comp_left (I J : UnitInterval) : (I.comp J).left = I.left + I.width * J.left := rfl

theorem comp_left_ge (I J : UnitInterval) : I.left ≤ (I.comp J).left := by
  simp only [comp_left]
  exact le_add_of_nonneg_right (mul_nonneg I.width_nonneg J.left_nonneg)

theorem comp_right_le (I J : UnitInterval) :
    (I.comp J).left + (I.comp J).width ≤ I.left + I.width := by
  have h := mul_le_mul_of_nonneg_left J.right_le_one I.width_nonneg
  simp only [comp_left, comp_width]
  nlinarith

/-- Ordered parent intervals remain ordered after arbitrary refinements. -/
theorem separated_comp (I J U V : UnitInterval)
    (h : I.left + I.width ≤ J.left) :
    (I.comp U).left + (I.comp U).width ≤ (J.comp V).left :=
  (comp_right_le I U).trans (h.trans (comp_left_ge J V))

/-- A common outer map preserves the order of interval endpoints. -/
theorem comp_separated (P I J : UnitInterval)
    (h : I.left + I.width ≤ J.left) :
    (P.comp I).left + (P.comp I).width ≤ (P.comp J).left := by
  have hmul := mul_le_mul_of_nonneg_left h P.width_nonneg
  simp only [comp_left, comp_width]
  nlinarith

noncomputable def word : List UnitInterval → UnitInterval
  | [] => unit
  | I :: tail => I.comp (word tail)

@[simp] theorem word_width (l : List UnitInterval) :
    (word l).width = (l.map UnitInterval.width).prod := by
  induction l with
  | nil => rfl
  | cons I l ih => simp only [word, comp_width, List.map_cons, List.prod_cons, ih]

theorem word_append_left (pre tail : List UnitInterval) :
    (word (pre ++ tail)).left = (word pre).left + (word pre).width * (word tail).left := by
  induction pre with
  | nil => simp [word, unit]
  | cons I pre ih => simp only [List.cons_append, word, comp_left, comp_width, ih]; ring

theorem word_append_width (pre tail : List UnitInterval) :
    (word (pre ++ tail)).width = (word pre).width * (word tail).width := by
  simp [word_width]

/-- The first unequal local interval orders the full composed words. -/
theorem word_first_difference (pre xs ys : List UnitInterval) (I J : UnitInterval)
    (h : I.left + I.width ≤ J.left) :
    (word (pre ++ I :: xs)).left + (word (pre ++ I :: xs)).width ≤
      (word (pre ++ J :: ys)).left := by
  have hsep := separated_comp I J (word xs) (word ys) h
  have hmul := mul_le_mul_of_nonneg_left hsep (word pre).width_nonneg
  simp only [word_append_left, word_append_width, word]
  simp only [comp_left, comp_width] at hmul ⊢
  nlinarith

/-- Every positive-width interval lies below the common rounded height. -/
theorem floor_rank_lt (I : UnitInterval) (ε : ℝ) (hε : 0 < ε) :
    ⌊I.left / ε⌋₊ < ⌈1 / ε⌉₊ := by
  exact Nat.floor_lt_ceil_of_lt_of_pos
    ((div_lt_div_iff_of_pos_right hε).mpr I.left_lt_one) (one_div_pos.mpr hε)

/-- Width at least ε forces a strict increase of the rounded left endpoint. -/
theorem floor_rank_lt_of_separated (I J : UnitInterval) (ε : ℝ) (hε : 0 < ε)
    (hw : ε ≤ I.width) (h : I.left + I.width ≤ J.left) :
    ⌊I.left / ε⌋₊ < ⌊J.left / ε⌋₊ := by
  have hnonneg : 0 ≤ I.left / ε := div_nonneg I.left_nonneg hε.le
  have hstep : I.left / ε + 1 ≤ J.left / ε := by
    apply (le_div_iff₀ hε).mpr
    have he : (I.left / ε + 1) * ε = I.left + ε := by field_simp
    rw [he]
    linarith
  have hfloor := Nat.floor_mono hstep
  rw [Nat.floor_add_one hnonneg] at hfloor
  omega
end UnitInterval
end NK
