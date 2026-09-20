import NK.LexicographicCapacity

/-! Capacity transport by vertex equivalence and exact first-difference word
capacity. The graph is defined literally by a first differing coordinate;
its recursive product description is proved from that definition. -/
namespace NK

universe u v

namespace DigraphAlphabet

variable {V : Type u} {W : Type v} {G : V → V → Prop} {H : W → W → Prop}

/-- Pull back actual intervals along an arc-preserving vertex map. -/
def pullback (B : DigraphAlphabet H) (e : V → W)
    (hrel : ∀ x y, G x y → H (e x) (e y)) : DigraphAlphabet G where
  interval x := B.interval (e x)
  ordered x y I J hI hJ hxy := B.ordered (e x) (e y) I J hI hJ (hrel x y hxy)

theorem pullback_moment [Fintype V] [Fintype W] (B : DigraphAlphabet H) (e : V ≃ W)
    (hrel : ∀ x y, G x y → H (e x) (e y)) (f : ℝ) :
    (pullback B e hrel).moment f = B.moment f :=
  e.sum_comp (fun x => weight f (B.interval x))

end DigraphAlphabet

namespace LexicographicCapacity

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable (G : V → V → Prop) (H : W → W → Prop)

/-- A bijective arc-preserving pullback gives the corresponding capacity inequality. -/
theorem capacity_le_of_pullback (e : V ≃ W)
    (hrel : ∀ x y, G x y → H (e x) (e y)) (f : ℝ) (hf : 0 ≤ f) :
    capacity H f ≤ capacity G f := by
  apply csSup_le (momentSet_nonempty H f)
  rintro z ⟨B,rfl⟩
  rw [← DigraphAlphabet.pullback_moment B e hrel f]
  exact moment_le_capacity G f hf (DigraphAlphabet.pullback B e hrel)

/-- Capacity depends only on the directed graph, not on its vertex encoding. -/
theorem capacity_equiv (e : V ≃ W)
    (hrel : ∀ x y, G x y ↔ H (e x) (e y)) (f : ℝ) (hf : 0 ≤ f) :
    capacity G f = capacity H f := by
  apply le_antisymm
  · apply capacity_le_of_pullback H G e.symm _ f hf
    intro x y hxy
    exact (hrel (e.symm x) (e.symm y)).mpr (by simpa only [Equiv.apply_symm_apply] using hxy)
  · exact capacity_le_of_pullback G H e (fun x y hxy => (hrel x y).mp hxy) f hf

end LexicographicCapacity

namespace WordGraphCapacity

variable {V : Type u}

/-- Literal least-coordinate arc relation. If G is irreflexive, the selected
coordinate is the first unequal coordinate. The definition also allows loops. -/
def wordArc (G : V → V → Prop) (e : ℕ) (x y : Fin e → V) : Prop :=
  ∃ j : Fin e, (∀ i : Fin e, i < j → x i = y i) ∧ G (x j) (y j)

/-- Split an actual function word into its first letter and remaining letters. -/
def split (n : ℕ) : (Fin (n+1) → V) ≃ V × (Fin n → V) where
  toFun x := (x 0, fun j => x j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by cases p; rfl

/-- The lexicographic recursion follows from the literal coordinate relation. -/
theorem wordArc_succ (G : V → V → Prop) (n : ℕ) (x y : Fin (n+1) → V) :
    wordArc G (n+1) x y ↔ DigraphAlphabet.lex G (wordArc G n) (split n x) (split n y) := by
  change wordArc G (n+1) x y ↔ G (x 0) (y 0) ∨
    (x 0 = y 0 ∧ wordArc G n (fun j => x j.succ) (fun j => y j.succ))
  constructor
  · rintro ⟨j,hpre,hj⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨t,rfl⟩
    · exact Or.inl hj
    · refine Or.inr ⟨hpre 0 (Nat.zero_lt_succ _), t, ?_, hj⟩
      intro i hi
      exact hpre i.succ (Fin.succ_lt_succ_iff.mpr hi)
  · rintro (hhead | ⟨hhead,j,hpre,hj⟩)
    · refine ⟨0, ?_, hhead⟩
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
    · refine ⟨j.succ, ?_, hj⟩
      intro i hi
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨t,rfl⟩
      · exact hhead
      · exact hpre t (Fin.succ_lt_succ_iff.mp hi)

/-- No coordinates means the one-vertex edgeless graph. -/
theorem wordArc_zero (G : V → V → Prop) : wordArc G 0 = (fun _ _ => False) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨j,_,_⟩
    exact Fin.elim0 j
  · intro h
    exact False.elim h

/-- Exact depth law for ordinary finite directed first-difference graphs. -/
theorem word_capacity [Fintype V] (G : V → V → Prop) (f : ℝ) (hf : 0 ≤ f) (e : ℕ) :
    LexicographicCapacity.capacity (wordArc G e) f = (LexicographicCapacity.capacity G f)^e := by
  induction e with
  | zero =>
    rw [wordArc_zero, LexicographicCapacity.capacity_edgeless f hf]
    simp
  | succ n ih =>
    calc
      LexicographicCapacity.capacity (wordArc G (n+1)) f =
          LexicographicCapacity.capacity (DigraphAlphabet.lex G (wordArc G n)) f :=
        LexicographicCapacity.capacity_equiv _ _ (split n) (wordArc_succ G n) f hf
      _ = LexicographicCapacity.capacity G f * LexicographicCapacity.capacity (wordArc G n) f :=
        LexicographicCapacity.capacity_lex G (wordArc G n) f hf
      _ = (LexicographicCapacity.capacity G f)^(n+1) := by rw [ih,pow_succ]; ring

end WordGraphCapacity
end NK
