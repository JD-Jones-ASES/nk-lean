import NK.Definitions

/-! # Uniform bounds for finite families of interval widths

Adjoining the width one-half makes the extrema well-defined even when the
index type is empty. No nonempty-family hypothesis or arbitrary default width
is hidden in the conclusion.
-/
namespace NK

universe u

/-- A finite family of widths strictly between zero and one admits one positive
lower bound and one strict upper bound; the empty family is included. -/
theorem exists_uniform_width_bounds {ι : Type u} [Finite ι]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i ∧ w i < 1) :
    ∃ σ ρ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ i, σ ≤ w i ∧ w i ≤ ρ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let S : Finset ℝ := insert (1 / 2) (Finset.univ.image w)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hbetween : ∀ x ∈ S, 0 < x ∧ x < 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hw i
  have hmin := hbetween (S.min' hS) (S.min'_mem hS)
  have hmax := hbetween (S.max' hS) (S.max'_mem hS)
  refine ⟨S.min' hS, S.max' hS, hmin.1, hmin.2.le, hmax.1, hmax.2, ?_⟩
  intro i
  have hi : w i ∈ S := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  exact ⟨S.min'_le (w i) hi, S.le_max' (w i) hi⟩

end NK
