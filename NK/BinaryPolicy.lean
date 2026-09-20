import NK.BinaryGlue
import NK.AlphabetSymmetries

/-! # Finite parity-window binary policies

An absent parity window forbids that parity. Every step is constructed by
the concrete four-branch alphabet gluing theorem. No Bellman identity or
asymptotic transfer is assumed.
-/

namespace NK.BinaryPolicy

abbrev State := Fin 2 → Option UnitInterval

def parity (x : ℕ) : Fin 2 := ⟨x % 2, Nat.mod_lt _ (by decide)⟩

def flip (p : Fin 2) : Fin 2 := ⟨(p.val + 1) % 2, Nat.mod_lt _ (by decide)⟩

@[simp] theorem flip_flip (p : Fin 2) : flip (flip p) = p := by
  apply Fin.ext
  have hp := p.isLt
  dsimp [flip]
  omega

/-- Closed containment of one positive interval in another. -/
def Contains (J I : UnitInterval) : Prop :=
  J.left ≤ I.left ∧ I.left + I.width ≤ J.left + J.width

def InWindow (w : Option UnitInterval) (I : UnitInterval) : Prop :=
  ∃ J, w = some J ∧ Contains J I

def Fits {M : ℕ} (A : IntervalAlphabet 2 M) (W : State) : Prop :=
  ∀ x (hx : x ∈ A.support), InWindow (W (parity x)) (A.interval x hx)

theorem contains_refl (I : UnitInterval) : Contains I I := ⟨le_rfl, le_rfl⟩

theorem contains_trans {I J K : UnitInterval} (hIJ : Contains I J) (hJK : Contains J K) :
    Contains I K := ⟨hIJ.1.trans hJK.1, hJK.2.trans hIJ.2⟩

theorem inWindow_trans {w : Option UnitInterval} {J I : UnitInterval}
    (hw : InWindow w J) (hJI : Contains J I) : InWindow w I := by
  obtain ⟨K, hK, hKJ⟩ := hw
  exact ⟨K, hK, contains_trans hKJ hJI⟩

theorem contains_reflect {J I : UnitInterval} (h : Contains J I) :
    Contains J.reflect I.reflect := by
  dsimp [Contains, UnitInterval.reflect] at *
  constructor <;> linarith [h.1, h.2]

theorem contains_comp (P : UnitInterval) {J I : UnitInterval} (h : Contains J I) :
    Contains (P.comp J) (P.comp I) := by
  dsimp [Contains, UnitInterval.comp] at *
  constructor <;> nlinarith [P.width_pos, h.1, h.2]

noncomputable def empty (M : ℕ) : IntervalAlphabet 2 M where
  support := ∅
  residue_lt := by simp
  interval := by intro x hx; simp at hx
  ordered := by intro x hx; simp at hx

@[simp] theorem empty_moment (M : ℕ) (f : ℝ) : (empty M).moment f = 0 := by
  simp [empty, IntervalAlphabet.moment]

theorem empty_fits (M : ℕ) (W : State) : Fits (empty M) W := by
  intro x hx
  simp [empty] at hx

noncomputable def singleton (p : Fin 2) (I : UnitInterval) : IntervalAlphabet 2 (4 ^ 1) where
  support := {p.val}
  residue_lt x hx := by
    have hx' : x = p.val := Finset.mem_singleton.mp hx
    have hp := p.isLt
    norm_num
    omega
  interval _ _ := I
  ordered x hx y hy harc := by
    have hx' := Finset.mem_singleton.mp hx
    have hy' := Finset.mem_singleton.mp hy
    exact False.elim (harc.1 (hx'.trans hy'.symm))

theorem singleton_fits (W : State) (p : Fin 2) (I : UnitInterval) (hI : W p = some I) :
    Fits (singleton p I) W := by
  intro x hx
  have hx' : x = p.val := Finset.mem_singleton.mp hx
  subst x
  have hp : parity p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
  rw [hp]
  exact ⟨I, hI, contains_refl I⟩

@[simp] theorem singleton_moment (p : Fin 2) (I : UnitInterval) (f : ℝ) :
    (singleton p I).moment f = I.width ^ f := by
  simp [singleton, IntervalAlphabet.moment]

theorem singleton_quarter (p : Fin 2) (I : UnitInterval) (f v : ℝ)
    (hf : f ≤ 1) (hv : v ≤ 1) (hI : (1 / 4 : ℝ) ≤ I.width) :
    (1 / 4 : ℝ) * v ≤ (singleton p I).moment f := by
  rw [singleton_moment]
  have hpow := Real.self_le_rpow_of_le_one I.width_pos.le I.width_le_one hf
  linarith

noncomputable def reflectState (W : State) : State :=
  fun p => (W p).map UnitInterval.reflect

def swapState (W : State) : State := fun p => W (flip p)

noncomputable def affineState (P : UnitInterval) (W : State) : State :=
  fun p => (W p).map P.comp

theorem reflect_fits {M : ℕ} (A : IntervalAlphabet 2 M) (W : State)
    (hM : 2 ∣ M) (hW : Fits A W) : Fits A.reflect (reflectState W) := by
  intro x hx
  obtain ⟨a, rfl⟩ := (A.mem_reflect_support x).mp hx
  rw [A.reflect_interval a hx]
  have hp : parity ((M - a.val) % M) = parity a.val :=
    Fin.ext (AlphabetSymmetries.reflect_parity M a.val hM (A.residue_lt _ a.property))
  rw [hp]
  obtain ⟨J, hJ, hJI⟩ := hW a.val a.property
  exact ⟨J.reflect, by simp [reflectState, hJ], contains_reflect hJI⟩

theorem translate_one_fits {M : ℕ} (A : IntervalAlphabet 2 M) (W : State)
    (hM : 2 ∣ M) (hW : Fits A W) : Fits (A.translate 1) (swapState W) := by
  intro x hx
  obtain ⟨a, rfl⟩ := (A.mem_translate_support 1 x).mp hx
  rw [A.translate_interval 1 a hx]
  have hp : parity ((a.val + 1) % M) = flip (parity a.val) :=
    Fin.ext (AlphabetSymmetries.translate_one_parity M a.val hM)
  simpa only [hp, swapState, flip_flip, IntervalAlphabet.letterInterval] using hW a.val a.property

theorem affine_fits {M : ℕ} (A : IntervalAlphabet 2 M) (W : State)
    (P : UnitInterval) (hW : Fits A W) :
    Fits (A.affine P.left P.width P.left_nonneg P.width_pos P.right_le_one) (affineState P W) := by
  intro x hx
  obtain ⟨J, hJ, hJI⟩ := hW x hx
  exact ⟨P.comp J, by simp [affineState, hJ], contains_comp P hJI⟩

noncomputable def orient {M : ℕ} (A : IntervalAlphabet 2 M) (swap reflect : Bool) :
    IntervalAlphabet 2 M :=
  let R := if reflect then A.reflect else A
  if swap then R.translate 1 else R

noncomputable def orientState (W : State) (swap reflect : Bool) : State :=
  let R := if reflect then reflectState W else W
  if swap then swapState R else R

theorem orient_fits {M : ℕ} (A : IntervalAlphabet 2 M) (W : State)
    (swap reflect : Bool) (hM : 2 ∣ M) (hW : Fits A W) :
    Fits (orient A swap reflect) (orientState W swap reflect) := by
  cases swap <;> cases reflect
  · exact hW
  · exact reflect_fits A W hM hW
  · exact translate_one_fits A W hM hW
  · exact translate_one_fits A.reflect (reflectState W) hM (reflect_fits A W hM hW)

theorem orient_moment {M : ℕ} (A : IntervalAlphabet 2 M)
    (swap reflect : Bool) (f : ℝ) : (orient A swap reflect).moment f = A.moment f := by
  cases swap <;> cases reflect <;> simp [orient]

structure Transition (σ : Type*) where
  child : σ
  swap : Bool
  reflect : Bool
  placement : UnitInterval

noncomputable def Transition.state {σ : Type*} (t : Transition σ) (W : σ → State) : State :=
  affineState t.placement (orientState (W t.child) t.swap t.reflect)

noncomputable def Transition.alphabet {σ : Type*} {M : ℕ} (t : Transition σ)
    (A : σ → IntervalAlphabet 2 M) : IntervalAlphabet 2 M :=
  (orient (A t.child) t.swap t.reflect).affine t.placement.left t.placement.width
    t.placement.left_nonneg t.placement.width_pos t.placement.right_le_one

theorem Transition.fits {σ : Type*} {M : ℕ} (t : Transition σ)
    (A : σ → IntervalAlphabet 2 M) (W : σ → State) (hM : 2 ∣ M)
    (hW : ∀ j, Fits (A j) (W j)) : Fits (t.alphabet A) (t.state W) :=
  affine_fits _ _ _ (orient_fits _ _ _ _ hM (hW t.child))

theorem Transition.moment {σ : Type*} {M : ℕ} (t : Transition σ)
    (A : σ → IntervalAlphabet 2 M) (f : ℝ) :
    (t.alphabet A).moment f = t.placement.width ^ f * (A t.child).moment f := by
  rw [Transition.alphabet, IntervalAlphabet.affine_moment, orient_moment]

abbrev Row (σ : Type*) := Fin 4 → Option (Transition σ)

def slot (r : Fin 4) (p : Fin 2) : Fin 8 :=
  ⟨r.val + 4 * p.val, by have hr := r.isLt; have hp := p.isLt; omega⟩

def classBranch (c : Fin 8) : Fin 4 := ⟨c.val % 4, Nat.mod_lt _ (by decide)⟩
def classParity (c : Fin 8) : Fin 2 := ⟨c.val / 4, by have hc := c.isLt; omega⟩

@[simp] theorem classBranch_slot (r : Fin 4) (p : Fin 2) : classBranch (slot r p) = r := by
  apply Fin.ext
  dsimp [classBranch, slot]
  have hr := r.isLt
  omega

@[simp] theorem classParity_slot (r : Fin 4) (p : Fin 2) : classParity (slot r p) = p := by
  apply Fin.ext
  dsimp [classParity, slot]
  have hr := r.isLt
  omega

noncomputable def childWindows {σ : Type*} (W : σ → State) (row : Row σ) (r : Fin 4) : State :=
  match row r with
  | none => fun _ => none
  | some t => t.state W

noncomputable def classWindow {σ : Type*} (W : σ → State) (row : Row σ)
    (c : Fin 8) : Option UnitInterval := childWindows W row (classBranch c) (classParity c)

@[simp] theorem classWindow_slot {σ : Type*} (W : σ → State) (row : Row σ)
    (r : Fin 4) (p : Fin 2) : classWindow W row (slot r p) = childWindows W row r p := by
  simp [classWindow]

noncomputable def children {σ : Type*} {M : ℕ} (A : σ → IntervalAlphabet 2 M)
    (row : Row σ) (r : Fin 4) : IntervalAlphabet 2 M :=
  match row r with
  | none => empty M
  | some t => t.alphabet A

theorem children_fits {σ : Type*} {M : ℕ} (A : σ → IntervalAlphabet 2 M)
    (W : σ → State) (row : Row σ) (hM : 2 ∣ M) (hW : ∀ j, Fits (A j) (W j))
    (r : Fin 4) : Fits (children A row r) (childWindows W row r) := by
  cases h : row r with
  | none => simpa [children, childWindows, h] using empty_fits M (fun _ => none)
  | some t => simpa [children, childWindows, h] using t.fits A W hM hW

/-- The geometric data needed by a row: containment in the parent parity
window and ordering of every pair of adjacent occupied numerical classes. -/
structure RowValid {σ : Type*} (W : σ → State) (parent : State) (row : Row σ) : Prop where
  inside : ∀ (c : Fin 8) (I : UnitInterval), classWindow W row c = some I →
    InWindow (parent (parity c.val)) I
  cycle : ∀ (c d : Fin 8) (I J : UnitInterval),
    classWindow W row c = some I → classWindow W row d = some J →
    (c.val + 1) % 8 = d.val → I.left + I.width ≤ J.left

noncomputable def windowLeft : Option UnitInterval → ℝ
  | none => 0
  | some I => I.left

noncomputable def windowRight : Option UnitInterval → ℝ
  | none => 0
  | some I => I.left + I.width

theorem two_dvd_four_pow (m : ℕ) (hm : 1 ≤ m) : 2 ∣ 4 ^ m :=
  dvd_trans (by decide : 2 ∣ 4) (dvd_pow_self 4 (by omega))

theorem point_fits {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (row : Row σ) (hm : 1 ≤ m) (hW : ∀ j, Fits (A j) (W j))
    (p : BinaryGlue.Point (children A row)) :
    InWindow (classWindow W row (BinaryGlue.parityClass (children A row) p))
      (BinaryGlue.pointInterval (children A row) p) := by
  have h := children_fits A W row (two_dvd_four_pow m hm) hW p.1 p.2.val p.2.property
  change InWindow (classWindow W row (slot p.1 (parity p.2.val))) _
  rwa [classWindow_slot]

theorem glue_inside {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (row : Row σ) (hm : 1 ≤ m) (hW : ∀ j, Fits (A j) (W j))
    (p : BinaryGlue.Point (children A row)) :
    windowLeft (classWindow W row (BinaryGlue.parityClass (children A row) p)) ≤
        (BinaryGlue.pointInterval (children A row) p).left ∧
      (BinaryGlue.pointInterval (children A row) p).left +
        (BinaryGlue.pointInterval (children A row) p).width ≤
          windowRight (classWindow W row (BinaryGlue.parityClass (children A row) p)) := by
  obtain ⟨I, hI, hIp⟩ := point_fits A W row hm hW p
  simpa [hI, windowLeft, windowRight, Contains] using hIp

theorem glue_cycle {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (parent : State) (row : Row σ) (hm : 1 ≤ m)
    (hW : ∀ j, Fits (A j) (W j)) (hv : RowValid W parent row)
    (p q : BinaryGlue.Point (children A row))
    (hpq : ((BinaryGlue.parityClass (children A row) p).val + 1) % 8 =
      (BinaryGlue.parityClass (children A row) q).val) :
    windowRight (classWindow W row (BinaryGlue.parityClass (children A row) p)) ≤
      windowLeft (classWindow W row (BinaryGlue.parityClass (children A row) q)) := by
  obtain ⟨I, hI, _⟩ := point_fits A W row hm hW p
  obtain ⟨J, hJ, _⟩ := point_fits A W row hm hW q
  simpa [hI, hJ, windowLeft, windowRight] using hv.cycle _ _ I J hI hJ hpq

noncomputable def step {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (parent : State) (row : Row σ) (hm : 1 ≤ m)
    (hW : ∀ j, Fits (A j) (W j)) (hv : RowValid W parent row) :
    IntervalAlphabet 2 (4 ^ (m + 1)) :=
  BinaryGlue.glue (children A row) hm
    (fun c => windowLeft (classWindow W row c))
    (fun c => windowRight (classWindow W row c))
    (glue_inside A W row hm hW) (glue_cycle A W parent row hm hW hv)

theorem parity_parityClass {m : ℕ} (A : Fin 4 → IntervalAlphabet 2 (4 ^ m))
    (p : BinaryGlue.Point A) :
    parity (BinaryGlue.parityClass A p).val = parity (BinaryGlue.encode A p) := by
  apply Fin.ext
  dsimp [parity]
  rw [BinaryGlue.parityClass_eq_mod]
  exact Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)

theorem step_fits {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (parent : State) (row : Row σ) (hm : 1 ≤ m)
    (hW : ∀ j, Fits (A j) (W j)) (hv : RowValid W parent row) :
    Fits (step A W parent row hm hW hv) parent := by
  intro x hx
  let p := BinaryGlue.decode (children A row) x hx
  have hp : BinaryGlue.encode (children A row) p = x := BinaryGlue.encode_decode _ _ _
  obtain ⟨I, hI, hIp⟩ := point_fits A W row hm hW p
  have hparent := hv.inside _ I hI
  have hfull := inWindow_trans hparent hIp
  rw [parity_parityClass, hp] at hfull
  exact hfull

noncomputable def rowMoment {σ : Type*} (row : Row σ) (f : ℝ) (v : σ → ℝ) : ℝ :=
  ∑ r : Fin 4, match row r with
    | none => 0
    | some t => t.placement.width ^ f * v t.child

theorem step_moment {σ : Type*} {m : ℕ} (A : σ → IntervalAlphabet 2 (4 ^ m))
    (W : σ → State) (parent : State) (row : Row σ) (hm : 1 ≤ m)
    (hW : ∀ j, Fits (A j) (W j)) (hv : RowValid W parent row) (f : ℝ) :
    (step A W parent row hm hW hv).moment f = rowMoment row f (fun j => (A j).moment f) := by
  rw [step, BinaryGlue.glue_moment]
  unfold rowMoment
  apply Finset.sum_congr rfl
  intro r _
  cases hr : row r with
  | none => simp [children, hr]
  | some t => simp [children, hr, Transition.moment]

/-- A final common half-scale gives every width strictly below one. -/
noncomputable def half {M : ℕ} (A : IntervalAlphabet 2 M) : IntervalAlphabet 2 M :=
  A.affine 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

theorem half_width_lt_one {M : ℕ} (A : IntervalAlphabet 2 M)
    (x : ℕ) (hx : x ∈ (half A).support) : ((half A).interval x hx).width < 1 := by
  change (1 / 2 : ℝ) * (A.interval x hx).width < 1
  linarith [(A.interval x hx).width_le_one]

theorem half_moment {M : ℕ} (A : IntervalAlphabet 2 M) (f : ℝ) :
    (half A).moment f = (1 / 2 : ℝ) ^ f * A.moment f :=
  A.affine_moment 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) f

end NK.BinaryPolicy
