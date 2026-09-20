import NK.SelectedBlock
import NK.CRTTransfer
import NK.MomentProducts
import NK.RankBudget
import NK.UniformBounds

/-! # The finite interval-moment criterion

Every input is finite interval data and a real moment inequality. Concrete
stopping words supply the blocks used in the CRT construction; the strict
surplus pays the common rank cost and the finite-layer pigeonhole factors.
-/
namespace NK

/-- A finite component of the general kth-power interval criterion. -/
structure MomentComponent (k : ℕ) (α : ℝ) where
  base : ℕ
  root : ℕ
  base_ge_two : 2 ≤ base
  base_eq_power : base = root ^ k
  alphabet : IntervalAlphabet k base
  f : ℝ
  f_nonneg : 0 ≤ f
  width_lt_one : ∀ x (hx : x ∈ alphabet.support), (alphabet.interval x hx).width < 1
  moment_bound : (base : ℝ) ^ α ≤ alphabet.moment f

/-- The interval-moment criterion with explicit common finite width bounds. -/
theorem powerLowerBound_of_intervalMoments_uniform (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 ≤ α) (l : List (MomentComponent k α))
    (hne : l ≠ []) (hco : (l.map (fun c => c.base)).Pairwise Nat.Coprime)
    (σ ρ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hlower : ∀ c ∈ l, ∀ x (hx : x ∈ c.alphabet.support),
      σ ≤ (c.alphabet.interval x hx).width)
    (hupper : ∀ c ∈ l, ∀ x (hx : x ∈ c.alphabet.support),
      (c.alphabet.interval x hx).width ≤ ρ)
    (hsurplus : α < (l.map (fun c => c.f)).sum) : PowerLowerBound k α := by
  classical
  obtain ⟨K, hK, hbudget⟩ := exists_common_rank_budget l.length σ ρ α
    (l.map (fun c => c.f)).sum (List.length_pos_iff_ne_nil.mpr hne) hσ hσ1 hρ hρ1 hα hsurplus
  let ι := {c : MomentComponent k α // c ∈ l}
  let L : List ι := l.attach
  have hex : ∀ i : ι, ∃ e : ℕ, 1 ≤ e ∧ e ≤ K ∧ ∃ C : Finset ℕ, ∃ h : ℕ → ℕ,
      KthPower.RankedBlock k (i.val.base ^ e) C h (intervalHeight (σ * ρ ^ K)) ∧
      C.Nonempty ∧
      ((i.val.base ^ e : ℕ) : ℝ) ^ α ≤
        ((K : ℝ) + 1) * (C.card : ℝ) * (ρ ^ K) ^ i.val.f := by
    intro i
    exact i.val.alphabet.exists_selected_rankedBlock i.val.root K i.val.f α σ ρ
      hk i.val.base_ge_two i.val.base_eq_power hK i.val.f_nonneg hα hσ
      (hlower i.val i.property) (hupper i.val i.property) hρ hρ1 i.val.moment_bound
  choose e he1 heK C rank hblocks hnonempty hmass using hex
  let H := intervalHeight (σ * ρ ^ K)
  let block : ι → KthPower.Block := fun i => (i.val.base ^ e i, C i, rank i, H)
  let blocks := L.map block
  have hH : 1 ≤ H := intervalHeight_pos _ (mul_pos hσ (pow_pos hρ K))
  have hLlen : L.length = l.length := List.length_attach
  have hLbase : L.map (fun i => i.val.base) = l.map (fun c => c.base) :=
    List.attach_map_val
  have hLf : L.map (fun i => i.val.f) = l.map (fun c => c.f) := List.attach_map_val
  have hbco : (blocks.map Prod.fst).Pairwise Nat.Coprime := by
    simp only [blocks, List.map_map, block, Function.comp_def]
    apply List.pairwise_map.mpr
    have hc := List.pairwise_map.mp (show (L.map (fun i => i.val.base)).Pairwise
      Nat.Coprime by rw [hLbase]; exact hco)
    exact hc.imp (fun {i j} hij => hij.pow (e i) (e j))
  have hheight : 1 + (blocks.map (fun b => b.2.2.2 - 1)).sum =
      1 + l.length * (H - 1) := by
    simp [blocks, block, Function.comp_def, List.sum_replicate, hLlen]
  have hcard : ∀ b ∈ blocks, 1 ≤ b.2.1.card := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact Finset.one_le_card.mpr (hnonempty i)
  have hpow : ∀ b ∈ blocks, ∃ n : ℕ, b.1 = n ^ k := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    refine ⟨i.val.root ^ e i, ?_⟩
    simp only [block, i.val.base_eq_power, ← pow_mul, Nat.mul_comm k (e i)]
  have hcounts :
      (((blocks.map Prod.fst).prod : ℕ) : ℝ) ^ α ≤
        ((K : ℝ) + 1) ^ l.length *
          (((blocks.map (fun b => b.2.1.card)).prod : ℕ) : ℝ) *
          (ρ ^ K) ^ (l.map (fun c => c.f)).sum := by
    have hm := list_moment_product L
      (fun i => ((i.val.base ^ e i : ℕ) : ℝ) ^ α)
      (fun i => ((C i).card : ℝ)) (fun i => i.val.f)
      ((K : ℝ) + 1) (ρ ^ K) (by positivity) (pow_pos hρ K)
      (by intros; positivity) (by intros; positivity) (fun i _ => hmass i)
    rw [← list_prod_rpow L (fun i => ((i.val.base ^ e i : ℕ) : ℝ)) α
      (by intros; positivity), hLlen, hLf] at hm
    simpa only [Nat.cast_list_prod, blocks, List.map_map, block, Function.comp_def] using hm
  have hfinal :
      (((blocks.map Prod.fst).prod *
        (1 + (blocks.map (fun b => b.2.2.2 - 1)).sum) : ℕ) : ℝ) ^ α ≤
        (((blocks.map (fun b => b.2.1.card)).prod : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    apply absorb_rank_cost _ _ _ ((K : ℝ) + 1) (ρ ^ K)
      (l.map (fun c => c.f)).sum α l.length
      (by positivity) (by positivity) (by positivity) hcounts
    rw [hheight]
    exact hbudget
  have hmod1 : ∀ m ∈ blocks.map Prod.fst, 1 ≤ m := by
    intro m hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact le_trans (by have := i.val.base_ge_two; omega)
      (Nat.le_pow (by have := he1 i; omega))
  have hmod2 : 2 ≤ (blocks.map Prod.fst).prod := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil l hne
    let i : ι := ⟨c, hc⟩
    have hi : i ∈ L := List.mem_attach l i
    have hbmem : (block i).1 ∈ blocks.map Prod.fst := by
      apply List.mem_map.mpr
      exact ⟨block i, List.mem_map.mpr ⟨i, hi, rfl⟩, rfl⟩
    have htwo : 2 ≤ (block i).1 :=
      le_trans c.base_ge_two (Nat.le_pow (by have := he1 i; omega))
    exact htwo.trans (List.single_le_prod hmod1 _ hbmem)
  have hranked : ∀ b ∈ blocks,
      KthPower.RankedBlock k b.1 b.2.1 b.2.2.1 b.2.2.2 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hblocks i
  have hheights : ∀ b ∈ blocks, 1 ≤ b.2.2.2 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hH
  exact powerLowerBound_of_rankedBlocks k hk blocks hbco hranked hheights hpow hcard α hα
    (le_trans hmod2 (Nat.le_mul_of_pos_right _ (by omega))) hfinal

/-- The general finite-family interval-moment theorem. Strictly subunit widths
have common bounds automatically, so no uniform constants occur in the input. -/
theorem powerLowerBound_of_intervalMoments (k : ℕ) (α : ℝ)
    (hk : 1 ≤ k) (hα : 0 ≤ α) (l : List (MomentComponent k α))
    (hne : l ≠ []) (hco : (l.map (fun c => c.base)).Pairwise Nat.Coprime)
    (hsurplus : α < (l.map (fun c => c.f)).sum) : PowerLowerBound k α := by
  classical
  let ι := {c : MomentComponent k α // c ∈ l}
  let : Fintype ι := l.finite_toSet.fintype
  let W := (i : ι) × i.val.alphabet.Letter
  let w : W → ℝ := fun a => (a.1.val.alphabet.letterInterval a.2).width
  have hw : ∀ a : W, 0 < w a ∧ w a < 1 := by
    intro a
    exact ⟨(a.1.val.alphabet.letterInterval a.2).width_pos,
      a.1.val.width_lt_one a.2.val a.2.property⟩
  obtain ⟨σ, ρ, hσ, hσ1, hρ, hρ1, hbounds⟩ := exists_uniform_width_bounds w hw
  apply powerLowerBound_of_intervalMoments_uniform k α hk hα l hne hco
    σ ρ hσ hσ1 hρ hρ1 ?_ ?_ hsurplus
  · intro c hc x hx
    exact (hbounds ⟨⟨c, hc⟩, ⟨x, hx⟩⟩).1
  · intro c hc x hx
    exact (hbounds ⟨⟨c, hc⟩, ⟨x, hx⟩⟩).2

end NK
