import NK.BinaryPolicy

/-! # Actual alphabets at every depth from a finite binary policy

The induction constructs alphabets through `BinaryPolicy.step`. A positive
weighted row inequality is used only after that construction has supplied
the exact moment recurrence. The universal initial constant is one quarter.
-/

namespace NK.BinaryPolicy

/-- A single occupied parity window with enough room for the depth-one seed. -/
structure Seed (W : State) where
  parity : Fin 2
  interval : UnitInterval
  present : W parity = some interval
  quarter : (1 / 4 : ℝ) ≤ interval.width

/-- Geometry of a finite-state policy. The index type need not be finite for
the construction; a concrete finite certificate instantiates it with Fin n. -/
structure Policy (σ : Type*) where
  windows : σ → State
  rows : σ → Row σ
  valid : ∀ i, RowValid windows (windows i) (rows i)
  seed : ∀ i, Seed (windows i)

namespace Policy

variable {σ : Type*}

/-- Depth n+1, together with its proved parity-window containment. -/
noncomputable def realization (P : Policy σ) :
    (n : ℕ) → (i : σ) → {A : IntervalAlphabet 2 (4 ^ (n + 1)) // Fits A (P.windows i)}
  | 0, i => ⟨singleton (P.seed i).parity (P.seed i).interval,
      singleton_fits _ _ _ (P.seed i).present⟩
  | n + 1, i =>
    let A := fun j => (P.realization n j).val
    let hA := fun j => (P.realization n j).property
    ⟨step A P.windows (P.windows i) (P.rows i) (by omega) hA (P.valid i),
      step_fits A P.windows (P.windows i) (P.rows i) (by omega) hA (P.valid i)⟩

noncomputable def alphabet (P : Policy σ) (n : ℕ) (i : σ) :
    IntervalAlphabet 2 (4 ^ (n + 1)) := (P.realization n i).val

theorem alphabet_fits (P : Policy σ) (n : ℕ) (i : σ) :
    Fits (P.alphabet n i) (P.windows i) := (P.realization n i).property

theorem alphabet_zero_moment (P : Policy σ) (i : σ) (f : ℝ) :
    (P.alphabet 0 i).moment f = (P.seed i).interval.width ^ f :=
  singleton_moment _ _ _

theorem alphabet_succ_moment (P : Policy σ) (n : ℕ) (i : σ) (f : ℝ) :
    (P.alphabet (n + 1) i).moment f =
      rowMoment (P.rows i) f (fun j => (P.alphabet n j).moment f) :=
  step_moment (fun j => (P.realization n j).val) P.windows (P.windows i) (P.rows i)
    (by omega) (fun j => (P.realization n j).property) (P.valid i) f

end Policy

theorem rowMoment_mono {σ : Type*} (row : Row σ) (f : ℝ) (v w : σ → ℝ)
    (hvw : ∀ j, v j ≤ w j) : rowMoment row f v ≤ rowMoment row f w := by
  unfold rowMoment
  apply Finset.sum_le_sum
  intro r _
  cases hr : row r with
  | none => exact le_rfl
  | some t =>
    exact mul_le_mul_of_nonneg_left (hvw t.child) (Real.rpow_nonneg t.placement.width_pos.le f)

theorem rowMoment_smul {σ : Type*} (row : Row σ) (f c : ℝ) (v : σ → ℝ) :
    rowMoment row f (fun j => c * v j) = c * rowMoment row f v := by
  unfold rowMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  cases row r <;> ring

namespace Policy

variable {σ : Type*}

/-- Weighted rows imply a quantitative lower bound for the actual constructed
alphabet at every depth. No stationary-profile assumption is used. -/
theorem moment_lower (P : Policy σ) (f growth : ℝ) (v : σ → ℝ)
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (hgrowth : 0 < growth)
    (hv : ∀ i, 0 < v i ∧ v i ≤ 1)
    (hrow : ∀ i, growth * v i ≤ rowMoment (P.rows i) f v)
    (n : ℕ) (i : σ) :
    (1 / 4 : ℝ) * growth ^ n * v i ≤ (P.alphabet n i).moment f := by
  induction n generalizing i with
  | zero =>
    rw [P.alphabet_zero_moment]
    simpa only [pow_zero, mul_one, singleton_moment] using
      singleton_quarter (P.seed i).parity (P.seed i).interval f (v i)
        hf.2 (hv i).2 (P.seed i).quarter
  | succ n ih =>
    rw [P.alphabet_succ_moment]
    have hc : (0 : ℝ) ≤ (1 / 4 : ℝ) * growth ^ n := by positivity
    calc
      (1 / 4 : ℝ) * growth ^ (n + 1) * v i =
          ((1 / 4 : ℝ) * growth ^ n) * (growth * v i) := by ring
      _ ≤ ((1 / 4 : ℝ) * growth ^ n) * rowMoment (P.rows i) f v :=
        mul_le_mul_of_nonneg_left (hrow i) hc
      _ = rowMoment (P.rows i) f (fun j => ((1 / 4 : ℝ) * growth ^ n) * v j) :=
        (rowMoment_smul _ _ _ _).symm
      _ ≤ rowMoment (P.rows i) f (fun j => (P.alphabet n j).moment f) :=
        rowMoment_mono _ _ _ _ ih

/-- Every positive depth has a genuine ordered alphabet satisfying the state
windows and the certified moment bound. -/
theorem exists_depth (P : Policy σ) (f growth : ℝ) (v : σ → ℝ)
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (hgrowth : 0 < growth)
    (hv : ∀ i, 0 < v i ∧ v i ≤ 1)
    (hrow : ∀ i, growth * v i ≤ rowMoment (P.rows i) f v)
    (m : ℕ) (hm : 1 ≤ m) (i : σ) :
    ∃ A : IntervalAlphabet 2 (4 ^ m), Fits A (P.windows i) ∧
      (1 / 4 : ℝ) * growth ^ (m - 1) * v i ≤ A.moment f := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  refine ⟨P.alphabet n i, P.alphabet_fits n i, ?_⟩
  simpa using P.moment_lower f growth v hf hgrowth hv hrow n i

/-- Shrinking the final alphabet by one half enforces every width <1.
The additional moment factor is exactly (1/2)^f. -/
theorem exists_half_depth (P : Policy σ) (f growth : ℝ) (v : σ → ℝ)
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (hgrowth : 0 < growth)
    (hv : ∀ i, 0 < v i ∧ v i ≤ 1)
    (hrow : ∀ i, growth * v i ≤ rowMoment (P.rows i) f v)
    (m : ℕ) (hm : 1 ≤ m) (i : σ) :
    ∃ A : IntervalAlphabet 2 (4 ^ m),
      (∀ x (hx : x ∈ A.support), (A.interval x hx).width < 1) ∧
      (1 / 2 : ℝ) ^ f * (1 / 4 : ℝ) * growth ^ (m - 1) * v i ≤ A.moment f := by
  obtain ⟨A, _, hA⟩ := P.exists_depth f growth v hf hgrowth hv hrow m hm i
  refine ⟨half A, half_width_lt_one A, ?_⟩
  rw [half_moment]
  have h := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) f)
  simpa only [mul_assoc] using h

end Policy
end NK.BinaryPolicy
