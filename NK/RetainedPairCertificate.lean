import NK.RetainedCRTAlphabet

/-! # Pruned certificates for paired retained-word geometry

A binary tree records common prefixes and a lower bound for the starts of all
intervals below each node. A row query skips a node only when its interval ends
before that bound, or a fixed first unequal digit forbids every arc into the
node. All summaries and pruning decisions are verified by finite predicates.
-/
namespace NK

/-- Explicit indexed prefix equality, with a finite decision procedure. -/
def CertificateWordPrefix (u v : List ℕ) : Prop :=
  u.length ≤ v.length ∧ ∀ i : Fin u.length, u.getD i.val 0 = v.getD i.val 0

instance (u v : List ℕ) : Decidable (CertificateWordPrefix u v) := by
  unfold CertificateWordPrefix
  infer_instance

theorem CertificateWordPrefix.refl (u : List ℕ) : CertificateWordPrefix u u :=
  ⟨le_rfl, fun _ => rfl⟩

theorem CertificateWordPrefix.trans {u v w : List ℕ}
    (huv : CertificateWordPrefix u v) (hvw : CertificateWordPrefix v w) :
    CertificateWordPrefix u w := by
  refine ⟨huv.1.trans hvw.1, ?_⟩
  intro i
  exact (huv.2 i).trans (hvw.2 ⟨i.val, lt_of_lt_of_le i.isLt huv.1⟩)

/-- A fixed first unequal digit rules out every compatible extension of a prefix. -/
def CertificatePrefixBlocks (k m : ℕ) (v t : List ℕ) : Prop :=
  ∃ j : Fin t.length, j.val < v.length ∧ v.getD j.val 0 ≠ t.getD j.val 0 ∧
    (∀ i : Fin j.val, v.getD i.val 0 = t.getD i.val 0) ∧
    ¬ KthPower.IsNonzeroPowerMod k m (KthPower.diffMod m (v.getD j.val 0) (t.getD j.val 0))

instance (k m : ℕ) (v t : List ℕ) : Decidable (CertificatePrefixBlocks k m v t) := by
  unfold CertificatePrefixBlocks
  infer_instance

private theorem nonzeroPowerMod_of_powerArc (k m a b : ℕ) (ha : a < m) (hb : b < m)
    (h : PowerArc k m a b) : KthPower.IsNonzeroPowerMod k m (KthPower.diffMod m a b) := by
  obtain ⟨hne, z, hz⟩ := h
  have hm : 0 < m := by omega
  rw [Nat.mod_eq_of_lt hb] at hz
  have hd := KthPower.diffMod_unique m a b (z ^ k) hm ha hb hz
  have hdlt := KthPower.diffMod_lt m a b hm
  refine ⟨?_, z % m, Nat.mod_lt _ hm, ?_⟩
  · rw [Nat.mod_eq_of_lt hdlt]
    exact KthPower.diffMod_ne_zero m a b ha hb hne
  · rw [← Nat.pow_mod, ← hd, Nat.mod_eq_of_lt hdlt]

private theorem certificate_getD_lt (m : ℕ) (v : List ℕ) (hv : ∀ a ∈ v, a < m)
    (j : ℕ) (hj : j < v.length) : v.getD j 0 < m := by
  rw [List.getD_eq_getElem _ _ hj]
  exact hv _ (List.getElem_mem hj)

/-- Soundness of one prefix-based exclusion. -/
theorem CertificatePrefixBlocks.not_compatible {k m : ℕ} {v t w : List ℕ}
    (hblock : CertificatePrefixBlocks k m v t) (hprefix : CertificateWordPrefix t w)
    (hv : ∀ a ∈ v, a < m) (hw : ∀ a ∈ w, a < m)
    (harc : v = w ∨ FirstDifferencePowerArc k m v w) : False := by
  obtain ⟨j, hjv, hjne, hjlow, hjpower⟩ := hblock
  have hjword : t.getD j.val 0 = w.getD j.val 0 := hprefix.2 j
  rcases harc with rfl | ⟨hlen, r, hr, hrlow, hrpower⟩
  · exact hjne hjword.symm
  · rcases lt_trichotomy j.val r with hjr | hjr | hrj
    · exact hjne ((hrlow j.val hjr).trans hjword.symm)
    · subst r
      apply hjpower
      rw [hjword]
      exact nonzeroPowerMod_of_powerArc k m _ _
        (certificate_getD_lt m v hv j.val hjv)
        (certificate_getD_lt m w hw j.val (lt_of_lt_of_le j.isLt hprefix.1)) hrpower
    · apply hrpower.1
      exact (hjlow ⟨r, hrj⟩).trans
        (hprefix.2 ⟨r, lt_trans hrj j.isLt⟩)

/-- One literal integer interval row. Words are low digit first. -/
structure PairCertificateRow where
  word : RetainedPair
  start : ℕ
  width : ℕ
  deriving DecidableEq

/-- A generator may choose any binary partition. Its node annotations are checked. -/
inductive PairCertificateTree where
  | leaf (row : PairCertificateRow)
  | branch (pPrefix qPrefix : List ℕ) (minStart : ℕ)
      (left right : PairCertificateTree)

namespace PairCertificateTree

def pPrefix : PairCertificateTree → List ℕ
  | .leaf r => r.word.1
  | .branch a _ _ _ _ => a

def qPrefix : PairCertificateTree → List ℕ
  | .leaf r => r.word.2
  | .branch _ b _ _ _ => b

def minStart : PairCertificateTree → ℕ
  | .leaf r => r.start
  | .branch _ _ s _ _ => s

def rows : PairCertificateTree → List PairCertificateRow
  | .leaf r => [r]
  | .branch _ _ _ l r => l.rows ++ r.rows

/-- Pure finite row validation; the common denominator is supplied separately. -/
def RowValid (p q e D : ℕ) (r : PairCertificateRow) : Prop :=
  r.word.1.length = e ∧ r.word.2.length = e ∧
    (∀ a ∈ r.word.1, a < p) ∧ (∀ a ∈ r.word.2, a < q) ∧
    0 < r.width ∧ r.width < D ∧ r.start + r.width ≤ D

instance (p q e D : ℕ) (r : PairCertificateRow) : Decidable (RowValid p q e D r) := by
  unfold RowValid
  infer_instance

/-- Each node summary follows from its child summaries; leaves validate literal rows. -/
def Valid (p q e D : ℕ) : PairCertificateTree → Prop
  | .leaf r => RowValid p q e D r
  | .branch a b s l r =>
    CertificateWordPrefix a l.pPrefix ∧ CertificateWordPrefix a r.pPrefix ∧
    CertificateWordPrefix b l.qPrefix ∧ CertificateWordPrefix b r.qPrefix ∧
    s ≤ l.minStart ∧ s ≤ r.minStart ∧ Valid p q e D l ∧ Valid p q e D r

instance instDecidableValid (p q e D : ℕ) : (t : PairCertificateTree) → Decidable (Valid p q e D t)
  | .leaf r => inferInstanceAs (Decidable (RowValid p q e D r))
  | .branch a b s l r => by
    letI := instDecidableValid p q e D l
    letI := instDecidableValid p q e D r
    unfold Valid
    infer_instance

/-- Valid summaries hold for every row below the node. -/
theorem valid_row {p q e D : ℕ} {t : PairCertificateTree} (ht : t.Valid p q e D)
    {r : PairCertificateRow} (hr : r ∈ t.rows) :
    RowValid p q e D r ∧ CertificateWordPrefix t.pPrefix r.word.1 ∧
      CertificateWordPrefix t.qPrefix r.word.2 ∧ t.minStart ≤ r.start := by
  induction t with
  | leaf a =>
    have heq : r = a := by simpa [rows] using hr
    subst r
    exact ⟨ht, CertificateWordPrefix.refl _, CertificateWordPrefix.refl _, le_rfl⟩
  | branch a b s l v ihl ihv =>
    obtain ⟨hal, hav, hbl, hbv, hsl, hsv, hl, hv⟩ := ht
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨hrow, hpa, hqa, hstart⟩ := ihl hl hr
      exact ⟨hrow, hal.trans hpa, hbl.trans hqa, hsl.trans hstart⟩
    · obtain ⟨hrow, hpa, hqa, hstart⟩ := ihv hv hr
      exact ⟨hrow, hav.trans hpa, hbv.trans hqa, hsv.trans hstart⟩

/-- A query explores only nodes not discharged by their checked summaries. -/
def Query (k p q : ℕ) (source : PairCertificateRow) (t : PairCertificateTree) : Bool :=
  if source.start + source.width ≤ t.minStart then true
  else if CertificatePrefixBlocks k p source.word.1 t.pPrefix then true
  else if CertificatePrefixBlocks k q source.word.2 t.qPrefix then true
  else match t with
    | .leaf target => decide (source.word = target.word)
    | .branch _ _ _ l r => Query k p q source l && Query k p q source r

/-- A successful pruned query orders every actual target arc. -/
theorem query_sound {k p q e D : ℕ} {source : PairCertificateRow}
    (hs : RowValid p q e D source) {t : PairCertificateTree} (ht : t.Valid p q e D)
    (hquery : t.Query k p q source = true) {target : PairCertificateRow}
    (hmem : target ∈ t.rows) (harc : RetainedPairArc k p q source.word target.word) :
    source.start + source.width ≤ target.start := by
  induction t with
  | leaf r =>
    have heq : target = r := by simpa [rows] using hmem
    subst target
    obtain ⟨htrow, hpp, hqp, hstart⟩ := valid_row (r := r) ht hmem
    unfold Query at hquery
    split_ifs at hquery with hend hpblock hqblock
    · exact hend
    · exact False.elim (hpblock.not_compatible hpp hs.2.2.1 htrow.2.2.1 harc.2.1)
    · exact False.elim (hqblock.not_compatible hqp hs.2.2.2.1 htrow.2.2.2.1 harc.2.2)
    · exact False.elim (harc.1 (of_decide_eq_true hquery))
  | branch a b s l r ihl ihr =>
    obtain ⟨htrow, hpp, hqp, hstart⟩ := valid_row ht hmem
    have hl := ht.2.2.2.2.2.2.1
    have hr := ht.2.2.2.2.2.2.2
    unfold Query at hquery
    split_ifs at hquery with hend hpblock hqblock
    · exact hend.trans hstart
    · exact False.elim (hpblock.not_compatible hpp hs.2.2.1 htrow.2.2.1 harc.2.1)
    · exact False.elim (hqblock.not_compatible hqp hs.2.2.2.1 htrow.2.2.2.1 harc.2.2)
    · have hh := Bool.and_eq_true_iff.mp hquery
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihl hl hh.1 hmem
      · exact ihr hr hh.2 hmem

/-- Run one pruned query for every literal source row. -/
def GeometryValid (k p q : ℕ) (t : PairCertificateTree) : Bool :=
  t.rows.all (fun r => t.Query k p q r)

theorem geometryValid_sound {k p q e D : ℕ} {t : PairCertificateTree}
    (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true)
    {source target : PairCertificateRow} (hs : source ∈ t.rows) (hy : target ∈ t.rows)
    (harc : RetainedPairArc k p q source.word target.word) :
    source.start + source.width ≤ target.start := by
  apply query_sound (valid_row ht hs).1 ht _ hy harc
  exact (List.all_eq_true.mp hgeom) source hs

/-- Endpoint words permit linear-size local certificates of uniqueness. -/
def firstWord : PairCertificateTree → RetainedPair
  | .leaf r => r.word
  | .branch _ _ _ l _ => l.firstWord

def lastWord : PairCertificateTree → RetainedPair
  | .leaf r => r.word
  | .branch _ _ _ _ r => r.lastWord

/-- A strict key gap between children certifies distinct words without a
quadratic duplicate check. The key may be any fixed function of the word pair. -/
def Sorted (key : RetainedPair → ℕ) : PairCertificateTree → Bool
  | .leaf _ => true
  | .branch _ _ _ l r =>
    decide (key l.lastWord < key r.firstWord) && l.Sorted key && r.Sorted key

private theorem sorted_bounds_nodup (key : RetainedPair → ℕ) {t : PairCertificateTree}
    (hsort : t.Sorted key = true) :
    key t.firstWord ≤ key t.lastWord ∧
      (∀ a ∈ t.rows, key t.firstWord ≤ key a.word ∧ key a.word ≤ key t.lastWord) ∧
      (t.rows.map PairCertificateRow.word).Nodup := by
  induction t with
  | leaf r =>
    refine ⟨le_rfl, ?_, by simp [rows]⟩
    intro a ha
    have heq : a = r := by simpa [rows] using ha
    subst a
    exact ⟨le_rfl, le_rfl⟩
  | branch a b s l r ihl ihr =>
    simp only [Sorted, Bool.and_eq_true, decide_eq_true_eq] at hsort
    obtain ⟨⟨hgap, hl⟩, hr⟩ := hsort
    obtain ⟨hlspan, hlbounds, hlnodup⟩ := ihl hl
    obtain ⟨hrspan, hrbounds, hrnodup⟩ := ihr hr
    refine ⟨le_trans hlspan (le_trans hgap.le hrspan), ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hlo, hhi⟩ := hlbounds x hx
        exact ⟨hlo, le_trans hhi (le_trans hgap.le hrspan)⟩
      · obtain ⟨hlo, hhi⟩ := hrbounds x hx
        exact ⟨le_trans hlspan (le_trans hgap.le hlo), hhi⟩
    · simp only [rows, List.map_append, List.nodup_append]
      refine ⟨hlnodup, hrnodup, ?_⟩
      intro v hv w hw heq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
      have hxy : key x.word < key y.word :=
        lt_of_le_of_lt (hlbounds x hx).2 (lt_of_lt_of_le hgap (hrbounds y hy).1)
      exact (ne_of_lt hxy) (congrArg key heq)

/-- The cheap local sortedness checker proves uniqueness of all literal words. -/
theorem sorted_words_nodup (key : RetainedPair → ℕ) {t : PairCertificateTree}
    (hsort : t.Sorted key = true) : (t.rows.map PairCertificateRow.word).Nodup :=
  (sorted_bounds_nodup key hsort).2.2

/-- Literal words occurring in the certificate. No row multiplicity is hidden. -/
def wordSupport (t : PairCertificateTree) : Finset RetainedPair :=
  (t.rows.map PairCertificateRow.word).toFinset

private theorem exists_row_for_word (t : PairCertificateTree) (w : RetainedPair)
    (hw : w ∈ t.wordSupport) : ∃ r, r ∈ t.rows ∧ r.word = w :=
  List.mem_map.mp (List.mem_toFinset.mp hw)

noncomputable def rowForWord (t : PairCertificateTree) (w : RetainedPair)
    (hw : w ∈ t.wordSupport) : PairCertificateRow :=
  Classical.choose (exists_row_for_word t w hw)

theorem rowForWord_mem (t : PairCertificateTree) (w : RetainedPair)
    (hw : w ∈ t.wordSupport) : t.rowForWord w hw ∈ t.rows :=
  (Classical.choose_spec (exists_row_for_word t w hw)).1

theorem rowForWord_word (t : PairCertificateTree) (w : RetainedPair)
    (hw : w ∈ t.wordSupport) : (t.rowForWord w hw).word = w :=
  (Classical.choose_spec (exists_row_for_word t w hw)).2

private theorem rowForWord_valid {p q e D : ℕ} {t : PairCertificateTree}
    (ht : t.Valid p q e D) (w : RetainedPair) (hw : w ∈ t.wordSupport) :
    RowValid p q e D (t.rowForWord w hw) := (valid_row ht (t.rowForWord_mem w hw)).1

/-- Successful finite geometry checks construct the actual paired-word alphabet. -/
noncomputable def toAlphabet (t : PairCertificateTree) (k p q e D : ℕ)
    (hD : 0 < D) (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true) :
    RetainedPairAlphabet k p q e where
  support := t.wordSupport
  left_length := by
    intro w hw
    have hv := (rowForWord_valid ht w hw).1
    rwa [t.rowForWord_word w hw] at hv
  right_length := by
    intro w hw
    have hv := (rowForWord_valid ht w hw).2.1
    rwa [t.rowForWord_word w hw] at hv
  left_valid := by
    intro w hw
    have hv := (rowForWord_valid ht w hw).2.2.1
    rwa [t.rowForWord_word w hw] at hv
  right_valid := by
    intro w hw
    have hv := (rowForWord_valid ht w hw).2.2.2.1
    rwa [t.rowForWord_word w hw] at hv
  interval := fun w hw => {
    left := ((t.rowForWord w hw).start : ℝ) / D
    width := ((t.rowForWord w hw).width : ℝ) / D
    left_nonneg := by positivity
    width_pos := div_pos (by exact_mod_cast (rowForWord_valid ht w hw).2.2.2.2.1)
      (by exact_mod_cast hD)
    right_le_one := by
      rw [← add_div]
      apply (div_le_one (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
      exact_mod_cast (rowForWord_valid ht w hw).2.2.2.2.2.2 }
  ordered := by
    intro v hv w hw harc
    have hrowarc : RetainedPairArc k p q (t.rowForWord v hv).word (t.rowForWord w hw).word := by
      simpa only [rowForWord_word] using harc
    have h := geometryValid_sound ht hgeom (t.rowForWord_mem v hv) (t.rowForWord_mem w hw) hrowarc
    change ((t.rowForWord v hv).start : ℝ) / D + ((t.rowForWord v hv).width : ℝ) / D ≤
      ((t.rowForWord w hw).start : ℝ) / D
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D)
    exact_mod_cast h

/-- The interval width is the literal integer width divided by the common denominator. -/
@[simp] theorem toAlphabet_width (t : PairCertificateTree) (k p q e D : ℕ)
    (hD : 0 < D) (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true)
    (w : RetainedPair) (hw : w ∈ (t.toAlphabet k p q e D hD ht hgeom).support) :
    ((t.toAlphabet k p q e D hD ht hgeom).interval w hw).width =
      ((t.rowForWord w hw).width : ℝ) / D := rfl

theorem toAlphabet_width_lt_one (t : PairCertificateTree) (k p q e D : ℕ)
    (hD : 0 < D) (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true)
    (w : RetainedPair) (hw : w ∈ (t.toAlphabet k p q e D hD ht hgeom).support) :
    ((t.toAlphabet k p q e D hD ht hgeom).interval w hw).width < 1 := by
  rw [toAlphabet_width]
  apply (div_lt_one (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  exact_mod_cast (rowForWord_valid ht w hw).2.2.2.2.2.1

/-- With the cheap sortedness certificate, every literal row is selected unchanged. -/
theorem rowForWord_eq (key : RetainedPair → ℕ) {t : PairCertificateTree}
    (hsort : t.Sorted key = true) (r : PairCertificateRow) (hr : r ∈ t.rows)
    (hw : r.word ∈ t.wordSupport) : t.rowForWord r.word hw = r := by
  have hnodup := sorted_words_nodup key hsort
  have hinj := (List.nodup_map_iff_inj_on (List.Nodup.of_map PairCertificateRow.word hnodup)).mp hnodup
  exact hinj _ (t.rowForWord_mem r.word hw) r hr (t.rowForWord_word r.word hw)

/-- The actual compressed support has exactly the number of literal rows. -/
theorem toAlphabet_card (t : PairCertificateTree) (k p q e D : ℕ)
    (hD : 0 < D) (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true)
    (key : RetainedPair → ℕ) (hsort : t.Sorted key = true) :
    (t.toAlphabet k p q e D hD ht hgeom).support.card = t.rows.length := by
  change t.wordSupport.card = t.rows.length
  rw [wordSupport, List.toFinset_card_of_nodup (sorted_words_nodup key hsort), List.length_map]

/-- The compressed interval moment is exactly the sum over the literal rows. -/
theorem toAlphabet_moment (t : PairCertificateTree) (k p q e D : ℕ)
    (hD : 0 < D) (ht : t.Valid p q e D) (hgeom : t.GeometryValid k p q = true)
    (key : RetainedPair → ℕ) (hsort : t.Sorted key = true) (f : ℝ) :
    (t.toAlphabet k p q e D hD ht hgeom).moment f =
      (t.rows.map (fun r => ((r.width : ℝ) / D) ^ f)).sum := by
  classical
  let g : RetainedPair → ℝ := fun w =>
    if hw : w ∈ t.wordSupport then (((t.rowForWord w hw).width : ℝ) / D) ^ f else 0
  have hg (w : RetainedPair) (hw : w ∈ t.wordSupport) :
      g w = (((t.rowForWord w hw).width : ℝ) / D) ^ f := by simp only [g, dif_pos hw]
  have hmoment : (t.toAlphabet k p q e D hD ht hgeom).moment f = ∑ w ∈ t.wordSupport, g w := by
    rw [← Finset.sum_attach t.wordSupport g]
    unfold RetainedPairAlphabet.moment
    apply Finset.sum_congr rfl
    intro w _
    exact (hg w.val w.property).symm
  rw [hmoment, wordSupport, List.sum_toFinset g (sorted_words_nodup key hsort), List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hw : r.word ∈ t.wordSupport := List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
  change g r.word = _
  rw [hg r.word hw, rowForWord_eq key hsort r hr hw]

end PairCertificateTree
end NK
