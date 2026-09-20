import NK.BinaryPolicyGrowth

open NK NK.BinaryPolicy

#print axioms step
#print axioms step_fits
#print axioms step_moment
#print axioms Policy.moment_lower
#print axioms Policy.exists_half_depth

private def evenState : State := fun p => if p.val = 0 then some UnitInterval.unit else none
private def branch : Transition (Fin 1) := ⟨0, false, false, UnitInterval.unit⟩
private def evenRow : Row (Fin 1) := fun r => if r.val = 0 ∨ r.val = 2 then some branch else none

private theorem windows_exact (c : Fin 8) :
    classWindow (fun _ : Fin 1 => evenState) evenRow c =
      if c.val = 0 ∨ c.val = 2 then some UnitInterval.unit else none := by
  fin_cases c <;>
    simp [classWindow, classBranch, classParity, childWindows, evenRow, branch,
      Transition.state, orientState, affineState, evenState, UnitInterval.unit, UnitInterval.comp]

private theorem even_valid : RowValid (fun _ : Fin 1 => evenState) evenState evenRow where
  inside := by
    intro c I hI
    rw [windows_exact] at hI
    split_ifs at hI with hc
    · cases hI
      refine ⟨UnitInterval.unit, ?_, contains_refl _⟩
      rcases hc with hc | hc <;> simp [evenState, parity, hc]
  cycle := by
    intro c d I J hI hJ hnext
    rw [windows_exact] at hI hJ
    split_ifs at hI hJ with hc hd <;> grind

private def evenPolicy : Policy (Fin 1) where
  windows := fun _ => evenState
  rows := fun _ => evenRow
  valid := fun _ => even_valid
  seed := fun _ => ⟨0, UnitInterval.unit, by simp [evenState], by norm_num [UnitInterval.unit]⟩

private theorem row_two (f : ℝ) : rowMoment evenRow f (fun _ => 1) = 2 := by
  norm_num [rowMoment, Fin.sum_univ_succ, evenRow, branch, UnitInterval.unit]

example (m : ℕ) (hm : 1 ≤ m) :
    ∃ A : IntervalAlphabet 2 (4 ^ m),
      (∀ x (hx : x ∈ A.support), (A.interval x hx).width < 1) ∧
      (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (1 / 4) * 2 ^ (m - 1) ≤ A.moment (1 / 2) := by
  have h := evenPolicy.exists_half_depth (1 / 2) 2 (fun _ => 1)
    (by norm_num [Set.mem_Icc]) (by norm_num) (by intro i; norm_num)
    (by intro i; change 2 * 1 ≤ rowMoment evenRow (1 / 2) (fun _ => 1); rw [row_two]; norm_num)
    m hm 0
  simpa only [mul_one] using h

-- A present even-only window forbids a singleton of odd parity.
example : ¬ Fits (singleton (1 : Fin 2) UnitInterval.unit) evenState := by
  intro h
  have hs := h 1 (by simp [BinaryPolicy.singleton])
  obtain ⟨I, hI, _⟩ := hs
  simp [evenState, parity] at hI

-- Quarter initialization cannot be claimed for an eighth-width interval.
private noncomputable def eighth : UnitInterval := ⟨0, 1 / 8, by norm_num, by norm_num, by norm_num⟩
example : ¬ ((1 / 4 : ℝ) ≤ eighth.width) := by norm_num [eighth]

-- Positive adjacent full windows fail the exact cycle ordering.
example : ¬ (UnitInterval.unit.left + UnitInterval.unit.width ≤ UnitInterval.unit.left) := by
  norm_num [UnitInterval.unit]
