import NK.Certificates.Odd215Data
import NK.PairMomentCertificate

/-! The exact low-word moment and its full retained-digit CRT component. -/
set_option maxHeartbeats 0
set_option maxRecDepth 32768
namespace NK.Certificates

theorem odd215_moment : (98771297640625:ℝ)^(75806770413 / 100000000000 : ℝ) ≤ (9938375:ℝ) *
    (odd215Tree.rows.map (fun r => ((r.width:ℝ)/99999974386028)^(26536176765267 / 1000000000000000 : ℝ))).sum := by
  simpa only [Nat.cast_ofNat] using (PairMomentCertificate.moment_bound 1000000000000000000000000 99999974386028 26536176765267 1000000000000000 98771297640625 9938375 75806770413 100000000000
    odd215Tree ⟨46, 8, 40632880412771682182284752737342100, 40632880412771682182695757825378861⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))


end NK.Certificates
