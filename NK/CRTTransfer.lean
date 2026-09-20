import NK.RankedTransfer
import RK.LemmaC

/-! The shared CRT height is additive across components. The resulting
perfect-power modulus, rather than its modulus-times-height range scale,
is the base used by the repeated ranked construction. -/
namespace NK

/-- A finite product of kth powers remains a kth power. -/
theorem list_prod_isPower (k : ℕ) (l : List ℕ)
    (h : ∀ b ∈ l, ∃ n : ℕ, b = n ^ k) :
    ∃ n : ℕ, l.prod = n ^ k := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons b bs ih =>
    obtain ⟨n, hn⟩ := h b List.mem_cons_self
    obtain ⟨r, hr⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact ⟨n*r, by simp only [List.prod_cons, hn, hr, mul_pow]⟩

/-- The exact ranked-block combination consumed by the interval argument.
The count and height in the hypothesis are the actual finite CRT quantities. -/
theorem powerLowerBound_of_rankedBlocks (k : ℕ) (hk : 1 ≤ k)
    (l : List KthPower.Block)
    (hco : (l.map Prod.fst).Pairwise Nat.Coprime)
    (hblocks : ∀ b ∈ l, KthPower.RankedBlock k b.1 b.2.1 b.2.2.1 b.2.2.2)
    (hheights : ∀ b ∈ l, 1 ≤ b.2.2.2)
    (hpowers : ∀ b ∈ l, ∃ n : ℕ, b.1 = n ^ k)
    (hcards : ∀ b ∈ l, 1 ≤ b.2.1.card)
    (α : ℝ) (hα : 0 ≤ α)
    (hscale : 2 ≤ (l.map Prod.fst).prod * (1 + (l.map (fun b => b.2.2.2-1)).sum))
    (hmoment : (((l.map Prod.fst).prod * (1 + (l.map (fun b => b.2.2.2-1)).sum) : ℕ) : ℝ) ^ α ≤
      ((l.map (fun b => b.2.1.card)).prod : ℕ)) :
    PowerLowerBound k α := by
  let B := KthPower.glueList l
  have hB : KthPower.RankedBlock k B.1 B.2.1 B.2.2.1 B.2.2.2 :=
    KthPower.glueList_rankedBlock k l hco hblocks hheights
  have hroot : ∃ n : ℕ, B.1 = n ^ k := by
    rw [show B.1 = (l.map Prod.fst).prod from KthPower.glueList_fst l]
    apply list_prod_isPower
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hpowers c hc
  obtain ⟨n, hn⟩ := hroot
  have hH : B.2.2.2 = 1 + (l.map (fun b => b.2.2.2-1)).sum :=
    KthPower.glueList_height l hheights
  have hC : B.2.1.card = (l.map (fun b => b.2.1.card)).prod :=
    KthPower.glueList_card l hco (fun b hb => (hblocks b hb).1)
  have hcpos : 1 ≤ B.2.1.card := by
    rw [hC]
    apply List.one_le_prod
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact hcards b hb
  have hmod : B.1 = (l.map Prod.fst).prod := KthPower.glueList_fst l
  exact powerLowerBound_of_rankedBlock k n B.1 hk hn B.2.1 B.2.2.1 B.2.2.2 hB
    (by omega) (by rw [hmod, hH]; exact hscale) hcpos α hα
    (by rw [hmod, hH, hC]; exact hmoment)

end NK
