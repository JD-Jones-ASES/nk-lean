import NK.Stopping

/-! # A concrete finite stopping tree

A word stores its most recently added letter first. Its width is the product of
its letter widths. Only words whose width is strictly above `δ` are extended;
the remaining children stop at that layer. Thus the recurrence below is proved
from finite sets of actual words, rather than assumed as an abstract hypothesis.
-/
namespace NK.StoppingWords

universe u
variable {ι : Type u}

/-- Product of the widths in a word, with the empty product equal to one. -/
def width (w : ι → ℝ) : List ι → ℝ
  | [] => 1
  | a :: v => w a * width w v

@[simp] theorem width_nil (w : ι → ℝ) : width w [] = 1 := rfl
@[simp] theorem width_cons (w : ι → ℝ) (a : ι) (v : List ι) :
    width w (a :: v) = w a * width w v := rfl

theorem width_pos (w : ι → ℝ) (hw : ∀ a, 0 < w a) (v : List ι) :
    0 < width w v := by
  induction v with
  | nil => norm_num
  | cons a v ih => exact mul_pos (hw a) ih

theorem width_eq_prod (w : ι → ℝ) (v : List ι) :
    width w v = (v.map w).prod := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [ih]

variable [Fintype ι] [DecidableEq ι]

/-- All one-letter extensions, without any imposed recurrence on their mass. -/
def extensions (E : Finset (List ι)) : Finset (List ι) :=
  (Finset.univ ×ˢ E).image (fun p : ι × List ι => p.1 :: p.2)

@[simp] theorem mem_extensions (E : Finset (List ι)) (v : List ι) :
    v ∈ extensions E ↔ ∃ a t, t ∈ E ∧ v = a :: t := by
  simp only [extensions, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
    true_and, Prod.exists]
  constructor
  · rintro ⟨a, t, ht, h⟩
    exact ⟨a, t, ht, h.symm⟩
  · rintro ⟨a, t, ht, h⟩
    exact ⟨a, t, ht, h.symm⟩

/-- Active words after `j` letters; the root is the empty word. -/
noncomputable def active (w : ι → ℝ) (δ : ℝ) : ℕ → Finset (List ι)
  | 0 => {[]}
  | j + 1 => by classical exact (extensions (active w δ j)).filter (fun v => δ < width w v)

/-- Words stopped by extension from active layer `j`, so their length is `j+1`. -/
noncomputable def stopped (w : ι → ℝ) (δ : ℝ) (j : ℕ) : Finset (List ι) := by
  classical
  exact (extensions (active w δ j)).filter (fun v => width w v ≤ δ)

/-- The f-moment of a concrete finite word set. -/
noncomputable def moment (w : ι → ℝ) (f : ℝ) (E : Finset (List ι)) : ℝ :=
  ∑ v ∈ E, width w v ^ f

/-- The one-letter alphabet moment. -/
noncomputable def alphabetMoment (w : ι → ℝ) (f : ℝ) : ℝ := ∑ a, w a ^ f

@[simp] theorem active_zero (w : ι → ℝ) (δ : ℝ) : active w δ 0 = {[]} := rfl

@[simp] theorem mem_active_succ (w : ι → ℝ) (δ : ℝ) (j : ℕ) (v : List ι) :
    v ∈ active w δ (j+1) ↔ v ∈ extensions (active w δ j) ∧ δ < width w v := by
  classical
  exact Finset.mem_filter

@[simp] theorem mem_stopped (w : ι → ℝ) (δ : ℝ) (j : ℕ) (v : List ι) :
    v ∈ stopped w δ j ↔ v ∈ extensions (active w δ j) ∧ width w v ≤ δ := by
  classical
  exact Finset.mem_filter

theorem active_length (w : ι → ℝ) (δ : ℝ) (j : ℕ) :
    ∀ v ∈ active w δ j, v.length = j := by
  induction j with
  | zero => intro v hv; simpa using hv
  | succ j ih =>
    intro v hv
    obtain ⟨he, _⟩ := (mem_active_succ w δ j v).mp hv
    obtain ⟨a, t, ht, rfl⟩ := (mem_extensions _ _).mp he
    simp [ih t ht]

theorem stopped_length (w : ι → ℝ) (δ : ℝ) (j : ℕ) :
    ∀ v ∈ stopped w δ j, v.length = j+1 := by
  intro v hv
  obtain ⟨he, _⟩ := (mem_stopped w δ j v).mp hv
  obtain ⟨a, t, ht, rfl⟩ := (mem_extensions _ _).mp he
  simp [active_length w δ j t ht]

theorem active_width_gt (w : ι → ℝ) (δ : ℝ) (hδ : δ < 1) (j : ℕ) :
    ∀ v ∈ active w δ j, δ < width w v := by
  cases j with
  | zero =>
    intro v hv
    have hv' : v = [] := by simpa using hv
    simpa [hv'] using hδ
  | succ j => intro v hv; exact ((mem_active_succ w δ j v).mp hv).2

theorem stopped_width_le (w : ι → ℝ) (δ : ℝ) (j : ℕ) (v : List ι)
    (hv : v ∈ stopped w δ j) : width w v ≤ δ :=
  ((mem_stopped w δ j v).mp hv).2

/-- First crossing cannot reduce the width by more than one letter factor. -/
theorem stopped_width_gt (w : ι → ℝ) (δ σ : ℝ)
    (hδ : δ < 1) (hσ : 0 < σ) (hw : ∀ a, σ ≤ w a)
    (j : ℕ) (v : List ι) (hv : v ∈ stopped w δ j) :
    σ * δ < width w v := by
  obtain ⟨he, _⟩ := (mem_stopped w δ j v).mp hv
  obtain ⟨a, t, ht, rfl⟩ := (mem_extensions _ _).mp he
  have hp := active_width_gt w δ hδ j t ht
  have htpos := width_pos w (fun a => lt_of_lt_of_le hσ (hw a)) t
  calc
    σ * δ < σ * width w t := mul_lt_mul_of_pos_left hp hσ
    _ ≤ w a * width w t := mul_le_mul_of_nonneg_right (hw a) (le_of_lt htpos)
    _ = width w (a :: t) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem width_le_pow (w : ι → ℝ) (ρ : ℝ)
    (hw0 : ∀ a, 0 < w a) (hwρ : ∀ a, w a ≤ ρ) (hρ : 0 ≤ ρ)
    (v : List ι) : width w v ≤ ρ ^ v.length := by
  induction v with
  | nil => simp
  | cons a v ih =>
    simp only [width_cons, List.length_cons, pow_succ]
    calc
      w a * width w v ≤ ρ * (ρ ^ v.length) :=
        mul_le_mul (hwρ a) ih (le_of_lt (width_pos w hw0 v)) hρ
      _ = ρ ^ v.length * ρ := mul_comm _ _

/-- Every length-K word has already crossed the cutoff `ρ^K`. -/
theorem active_horizon_empty (w : ι → ℝ) (ρ : ℝ) (K : ℕ)
    (hK : 1 ≤ K) (hw0 : ∀ a, 0 < w a) (hwρ : ∀ a, w a ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : active w (ρ ^ K) K = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hcut : ρ ^ K < 1 := pow_lt_one₀ hρ0 hρ1 (by omega)
  have hgt := active_width_gt w (ρ ^ K) hcut K v hv
  have hle := width_le_pow w ρ hw0 hwρ hρ0 v
  rw [active_length w (ρ ^ K) K v hv] at hle
  exact (not_lt_of_ge hle) hgt

omit [Fintype ι] [DecidableEq ι] in
theorem moment_nonneg (w : ι → ℝ) (f : ℝ) (hw0 : ∀ a, 0 < w a)
    (E : Finset (List ι)) : 0 ≤ moment w f E := by
  apply Finset.sum_nonneg
  intro v _
  exact Real.rpow_nonneg (le_of_lt (width_pos w hw0 v)) f

@[simp] theorem moment_root (w : ι → ℝ) (f δ : ℝ) :
    moment w f (active w δ 0) = 1 := by simp [moment]

/-- Independent finite-product identity: every letter extends every active word. -/
theorem moment_extensions (w : ι → ℝ) (f : ℝ) (hw0 : ∀ a, 0 < w a)
    (E : Finset (List ι)) :
    moment w f (extensions E) = alphabetMoment w f * moment w f E := by
  classical
  unfold moment extensions
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    simp_rw [width_cons, Real.mul_rpow (le_of_lt (hw0 _)) (le_of_lt (width_pos w hw0 _))]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, alphabetMoment]
  · intro a _ b _ hab
    exact Prod.ext (List.cons.inj hab).1 (List.cons.inj hab).2

/-- The stopping recurrence follows by partitioning the actual children. -/
theorem moment_recurrence (w : ι → ℝ) (f δ : ℝ) (hw0 : ∀ a, 0 < w a)
    (j : ℕ) :
    moment w f (active w δ (j+1)) + moment w f (stopped w δ j) =
      alphabetMoment w f * moment w f (active w δ j) := by
  classical
  rw [← moment_extensions w f hw0]
  change (∑ v ∈ (extensions (active w δ j)).filter (fun v => δ < width w v), width w v ^ f) +
    (∑ v ∈ (extensions (active w δ j)).filter (fun v => width w v ≤ δ), width w v ^ f) =
    ∑ v ∈ extensions (active w δ j), width w v ^ f
  simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not
    (extensions (active w δ j)) (fun v => δ < width w v) (fun v => width w v ^ f)

/-- Each stopped word contributes at most the cutoff raised to `f`. -/
theorem stopped_moment_le (w : ι → ℝ) (f δ : ℝ) (hw0 : ∀ a, 0 < w a)
    (hf : 0 ≤ f) (j : ℕ) :
    moment w f (stopped w δ j) ≤ ((stopped w δ j).card : ℝ) * δ ^ f := by
  unfold moment
  calc
    _ ≤ ∑ _v ∈ stopped w δ j, δ ^ f := by
      apply Finset.sum_le_sum
      intro v hv
      exact Real.rpow_le_rpow (le_of_lt (width_pos w hw0 v))
        (stopped_width_le w δ j v hv) hf
    _ = _ := by simp

/-- The actual stopping tree has a layer with the stated cardinality bound. -/
theorem exists_stopped_layer (w : ι → ℝ) (K : ℕ) (f ρ q : ℝ)
    (hK : 1 ≤ K) (hw0 : ∀ a, 0 < w a) (hwρ : ∀ a, w a ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hf : 0 ≤ f)
    (hq : 1 ≤ q) (hqZ : q ≤ alphabetMoment w f) :
    ∃ j, j < K ∧ q ^ (j+1) ≤
      ((K : ℝ) + 1) * ((stopped w (ρ ^ K) j).card : ℝ) * (ρ ^ K) ^ f := by
  let A : ℕ → ℝ := fun j => moment w f (active w (ρ ^ K) j)
  let T : ℕ → ℝ := fun j => moment w f (stopped w (ρ ^ K) j)
  have hA : ∀ j, 0 ≤ A j := fun j => moment_nonneg w f hw0 _
  have hT : ∀ j, 0 ≤ T j := fun j => moment_nonneg w f hw0 _
  have hA0 : A 0 = 1 := moment_root w f (ρ ^ K)
  have hAK : A K = 0 := by
    dsimp [A]
    rw [active_horizon_empty w ρ K hK hw0 hwρ hρ0 hρ1]
    simp [moment]
  have hrec : ∀ j, j < K → q * A j ≤ A (j+1) + T j := by
    intro j _
    calc
      q * A j ≤ alphabetMoment w f * A j := mul_le_mul_of_nonneg_right hqZ (hA j)
      _ = A (j+1) + T j := (moment_recurrence w f (ρ ^ K) hw0 j).symm
  obtain ⟨j, hj, hmass⟩ := NK.stopping_mass K q A T hK hq hA hT hA0 hAK hrec
  refine ⟨j, hj, le_trans hmass ?_⟩
  have h := mul_le_mul_of_nonneg_left (stopped_moment_le w f (ρ ^ K) hw0 hf j)
    (show 0 ≤ (K : ℝ) + 1 by positivity)
  simpa only [T, mul_assoc] using h

/-- A terminal layer of actual finite words supplies the transfer-sized alphabet.
Its depth is between one and K, every word first crosses the cutoff there, and
its cardinality is bounded below by the stopping-mass argument. -/
theorem exists_terminal_layer (w : ι → ℝ) (K : ℕ) (f ρ σ b α : ℝ)
    (hK : 1 ≤ K) (hσ : 0 < σ) (hσw : ∀ a, σ ≤ w a)
    (hwρ : ∀ a, w a ≤ ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hf : 0 ≤ f) (hb : 1 ≤ b) (hα : 0 ≤ α)
    (hZ : b ^ α ≤ alphabetMoment w f) :
    ∃ e : ℕ, 1 ≤ e ∧ e ≤ K ∧ ∃ E : Finset (List ι),
      E = stopped w (ρ ^ K) (e-1) ∧
      (∀ v ∈ E, v.length = e ∧ σ * ρ ^ K < width w v ∧ width w v ≤ ρ ^ K) ∧
      b ^ ((e : ℝ) * α) ≤ ((K : ℝ) + 1) * (E.card : ℝ) * (ρ ^ K) ^ f := by
  have hw0 : ∀ a, 0 < w a := fun a => lt_of_lt_of_le hσ (hσw a)
  have hcut : ρ ^ K < 1 := pow_lt_one₀ hρ0 hρ1 (by omega)
  obtain ⟨j, hj, hmass⟩ := exists_stopped_layer w K f ρ (b ^ α) hK hw0 hwρ
    hρ0 hρ1 hf (Real.one_le_rpow hb hα) hZ
  refine ⟨j+1, by omega, by omega, stopped w (ρ ^ K) j, by simp, ?_, ?_⟩
  · intro v hv
    exact ⟨stopped_length w (ρ ^ K) j v hv,
      stopped_width_gt w (ρ ^ K) σ hcut hσ hσw j v hv,
      stopped_width_le w (ρ ^ K) j v hv⟩
  · have hb0 : 0 ≤ b := le_trans (by norm_num) hb
    rw [mul_comm ((j+1 : ℕ) : ℝ) α, Real.rpow_mul_natCast hb0 α (j+1)]
    exact hmass

end NK.StoppingWords
