import NK.PrimeBlockLex
import NK.WordGraphCapacity

/-! # Exact prime-depth interval capacity

This is the ordinary interval moment supremum over all selected residues and
all admissible positive intervals. The depth law is deduced from the proved
arithmetic graph isomorphism and the generic lexicographic capacity theorem;
no restricted support family or product-only interval ansatz is imposed.
-/
namespace NK

/-- Ordinary interval moment capacity of the full modular kth-power digraph. -/
noncomputable def modularCapacity (k m : ℕ) (f : ℝ) : ℝ :=
  LexicographicCapacity.capacity (fun x y : Fin m => PowerArc k m x.val y.val) f

/-- For every prime/exponent pair except binary squares, increasing the number
of full p^k blocks raises the one-block capacity to the same power. -/
theorem prime_block_capacity (p k e : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e) (f : ℝ) (hf : 0 ≤ f) :
    modularCapacity k ((p ^ k) ^ e) f = (modularCapacity k (p ^ k) f) ^ e := by
  let G := fun x y : Fin (p ^ k) => PowerArc k (p ^ k) x.val y.val
  have hP : 2 ≤ p ^ k := hp.two_le.trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hk)
  calc
    modularCapacity k ((p ^ k) ^ e) f =
        LexicographicCapacity.capacity (WordGraphCapacity.wordArc G e) f := by
      apply LexicographicCapacity.capacity_equiv _ _ (blockWordEquiv (p ^ k) e hP) _ f hf
      intro x y
      exact powerArc_iff_blockWord p k e hp hk hexception he x y hP
    _ = (modularCapacity k (p ^ k) f) ^ e := WordGraphCapacity.word_capacity G f hf e

/-- Equivalent prime-power notation for the complete depth law. -/
theorem prime_power_capacity (p k e : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e) (f : ℝ) (hf : 0 ≤ f) :
    modularCapacity k (p ^ (k * e)) f = (modularCapacity k (p ^ k) f) ^ e := by
  simpa only [pow_mul] using prime_block_capacity p k e hp hk hexception he f hf

/-- The depth barrier applies to every actual interval alphabet, including
arbitrary supports and widths, not only recursively constructed alphabets. -/
theorem prime_power_moment_le (p k e : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e) (f : ℝ) (hf : 0 ≤ f)
    (A : DigraphAlphabet (fun x y : Fin (p ^ (k * e)) =>
      PowerArc k (p ^ (k * e)) x.val y.val)) :
    A.moment f ≤ (modularCapacity k (p ^ k) f) ^ e := by
  calc
    A.moment f ≤ modularCapacity k (p ^ (k * e)) f :=
      LexicographicCapacity.moment_le_capacity _ f hf A
    _ = (modularCapacity k (p ^ k) f) ^ e := prime_power_capacity p k e hp hk hexception he f hf

namespace IntervalAlphabet

/-- The existing residue alphabet is an ordinary finite digraph alphabet,
with precisely its selected residues occupied. -/
noncomputable def toPowerDigraph {k m : ℕ} (A : IntervalAlphabet k m) :
    DigraphAlphabet (fun x y : Fin m => PowerArc k m x.val y.val) := by
  classical
  exact {
    interval := fun x => if hx : x.val ∈ A.support then some (A.interval x.val hx) else none
    ordered := by
      intro x y I J hI hJ harc
      have hx : x.val ∈ A.support := by
        by_contra hx
        simp only [dif_neg hx, reduceCtorEq] at hI
      have hy : y.val ∈ A.support := by
        by_contra hy
        simp only [dif_neg hy, reduceCtorEq] at hJ
      simp only [dif_pos hx, Option.some.injEq] at hI
      simp only [dif_pos hy, Option.some.injEq] at hJ
      rw [← hI, ← hJ]
      exact A.ordered x.val hx y.val hy harc }

/-- Conversion preserves the exact ordinary moment, with no interval change. -/
theorem toPowerDigraph_moment {k m : ℕ} (A : IntervalAlphabet k m) (f : ℝ) :
    A.toPowerDigraph.moment f = A.moment f := by
  classical
  let E : {x : Fin m // x.val ∈ A.support} ≃ ↥A.support := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, A.residue_lt x.val x.property⟩, x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  let w := fun x : Fin m => DigraphAlphabet.weight f (A.toPowerDigraph.interval x)
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x : Fin m => x.val ∈ A.support) w
  have hzero : (∑ x : {x : Fin m // x.val ∉ A.support}, w x.val) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp only [w, toPowerDigraph, dif_neg x.property, DigraphAlphabet.weight]
  rw [hzero, add_zero] at hsplit
  change (∑ x : Fin m, w x) = A.moment f
  rw [← hsplit]
  calc
    _ = ∑ x : {x : Fin m // x.val ∈ A.support}, (A.interval x.val.val x.property).width ^ f := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [w, toPowerDigraph, dif_pos x.property, DigraphAlphabet.weight]
    _ = ∑ x : ↥A.support, (A.interval x.val x.property).width ^ f :=
      E.sum_comp (fun x : ↥A.support => (A.interval x.val x.property).width ^ f)
    _ = A.moment f := by simp only [IntervalAlphabet.moment, Finset.attach_eq_univ]

/-- The exact prime-depth capacity barrier applies to the interval-alphabet
interface used throughout the arithmetic transfer and numerical certificates. -/
theorem moment_le_prime_power_capacity (p k e : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) (he : 1 ≤ e) (f : ℝ) (hf : 0 ≤ f)
    (A : IntervalAlphabet k (p ^ (k * e))) :
    A.moment f ≤ (modularCapacity k (p ^ k) f) ^ e := by
  rw [← A.toPowerDigraph_moment f]
  exact prime_power_moment_le p k e hp hk hexception he f hf A.toPowerDigraph

end IntervalAlphabet
end NK
