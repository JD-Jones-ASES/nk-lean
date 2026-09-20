import NK.RetainedPairCertificate

/-! # Verified bit-mask queries for retained-pair certificates

The finite mask table is checked once per modulus. Prefix comparison then
walks the two lists only until their first unequal entry, and tests one bit.
Soundness refines the existing certificate predicates and leaves the tree,
its summaries, and its interpretation unchanged.
-/

namespace NK

def PowerMaskValid (k m mask : ℕ) : Prop :=
  ∀ d : Fin m, mask.testBit d.val = decide (KthPower.IsNonzeroPowerMod k m d.val)

instance (k m mask : ℕ) : Decidable (PowerMaskValid k m mask) := by
  unfold PowerMaskValid
  infer_instance

/-- The first unequal entry determines the only possible prefix obstruction. -/
def FastPrefixBlocks (m mask : ℕ) : List ℕ → List ℕ → Bool
  | [], _ => false
  | _, [] => false
  | a :: v, b :: t =>
    if a = b then FastPrefixBlocks m mask v t
    else !(mask.testBit (KthPower.diffMod m a b))

private theorem prefixBlocks_cons (k m a : ℕ) (v t : List ℕ)
    (h : CertificatePrefixBlocks k m v t) : CertificatePrefixBlocks k m (a :: v) (a :: t) := by
  obtain ⟨j, hjv, hne, hlow, hpower⟩ := h
  refine ⟨⟨j.val + 1, by simp⟩, by simpa using hjv, ?_, ?_, ?_⟩
  · simpa using hne
  · intro i
    by_cases hi : i.val = 0
    · simp [hi]
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have hiLt : i.val < j.val + 1 := i.isLt
      have hrj : r < j.val := by omega
      simpa [hr] using hlow ⟨r, hrj⟩
  · simpa using hpower

/-- A successful bit-mask prefix test implies the original finite obstruction. -/
theorem fastPrefixBlocks_sound (k m mask : ℕ) (hm : 0 < m)
    (hmask : PowerMaskValid k m mask) (v t : List ℕ)
    (h : FastPrefixBlocks m mask v t = true) : CertificatePrefixBlocks k m v t := by
  induction v generalizing t with
  | nil => simp [FastPrefixBlocks] at h
  | cons a v ih =>
    cases t with
    | nil => simp [FastPrefixBlocks] at h
    | cons b t =>
      by_cases hab : a = b
      · subst b
        exact prefixBlocks_cons k m a v t (ih t (by simpa [FastPrefixBlocks] using h))
      · have hd := hmask ⟨KthPower.diffMod m a b, KthPower.diffMod_lt m a b hm⟩
        have hp : ¬ KthPower.IsNonzeroPowerMod k m (KthPower.diffMod m a b) := by
          simpa [FastPrefixBlocks, hab, hd] using h
        exact ⟨⟨0, by simp⟩, by simp, by simpa using hab, (fun i => Fin.elim0 i), by simpa using hp⟩

namespace PairCertificateTree

/-- The original query with its prefix decisions replaced by verified mask tests. -/
def FastQuery (k p q pMask qMask : ℕ) (source : PairCertificateRow) (t : PairCertificateTree) : Bool :=
  if source.start + source.width ≤ t.minStart then true
  else if FastPrefixBlocks p pMask source.word.1 t.pPrefix then true
  else if FastPrefixBlocks q qMask source.word.2 t.qPrefix then true
  else match t with
    | .leaf target => decide (source.word = target.word)
    | .branch _ _ _ l r =>
      FastQuery k p q pMask qMask source l && FastQuery k p q pMask qMask source r

theorem fastQuery_sound (k p q pMask qMask : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpMask : PowerMaskValid k p pMask) (hqMask : PowerMaskValid k q qMask)
    (source : PairCertificateRow) (t : PairCertificateTree)
    (h : t.FastQuery k p q pMask qMask source = true) : t.Query k p q source = true := by
  induction t with
  | leaf target =>
    rw [FastQuery] at h
    split_ifs at h with hend hpFast hqFast
    · rw [Query, if_pos hend]
    · have hb := fastPrefixBlocks_sound k p pMask hp hpMask _ _ hpFast
      rw [Query, if_neg hend, if_pos hb]
    · have hb := fastPrefixBlocks_sound k q qMask hq hqMask _ _ hqFast
      rw [Query, if_neg hend]
      split_ifs <;> simp_all
    · rw [Query, if_neg hend]
      split_ifs <;> simp_all
  | branch a b s l r ihl ihr =>
    rw [FastQuery] at h
    split_ifs at h with hend hpFast hqFast
    · rw [Query, if_pos hend]
    · have hb := fastPrefixBlocks_sound k p pMask hp hpMask _ _ hpFast
      rw [Query, if_neg hend, if_pos hb]
    · have hb := fastPrefixBlocks_sound k q qMask hq hqMask _ _ hqFast
      rw [Query, if_neg hend]
      split_ifs <;> simp_all
    · rw [Query, if_neg hend]
      split_ifs
      · rfl
      · rfl
      · exact Bool.and_eq_true_iff.mpr
          ⟨ihl (Bool.and_eq_true_iff.mp h).1, ihr (Bool.and_eq_true_iff.mp h).2⟩

def FastGeometryValid (k p q pMask qMask : ℕ) (t : PairCertificateTree) : Bool :=
  t.rows.all (fun source => t.FastQuery k p q pMask qMask source)

/-- The accelerated geometry checker is a sound refinement of the original checker. -/
theorem fastGeometryValid_sound (k p q pMask qMask : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpMask : PowerMaskValid k p pMask) (hqMask : PowerMaskValid k q qMask)
    (t : PairCertificateTree) (h : t.FastGeometryValid k p q pMask qMask = true) :
    t.GeometryValid k p q = true := by
  apply List.all_eq_true.mpr
  intro source hs
  exact fastQuery_sound k p q pMask qMask hp hq hpMask hqMask source t
    ((List.all_eq_true.mp h) source hs)

end PairCertificateTree
end NK
