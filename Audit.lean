import NK
import Lean.Util.CollectAxioms

/-! Development axiom audit, adapted from rk-lean's MIT-licensed Test/Axioms.
It checks all NK declarations and their transitive axiom dependencies. The
required-name check prevents a vacuous audit of an accidentally empty import.
This is an axiom audit, not a substitute for independent kernel replay. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "NK." || label.startsWith "_private.NK." then
      checked := checked + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 100 do
    logError m!"Only {checked} NK declarations imported; expected at least 100."
  for name in [`NK.powerLowerBound_of_geometric_witnesses,
      `NK.powerLowerBound_of_rankedBlock,
      `NK.dvd_pow_iff_perfectPowerClosure_dvd,
      `NK.IntervalAlphabet.closureLift_moment,
      `NK.StoppingWords.exists_terminal_layer,
      `NK.IntervalAlphabet.wordAlphabet_moment,
      `NK.IntervalAlphabet.exists_selected_rankedBlock,
      `NK.exists_common_rank_budget,
      `NK.powerLowerBound_of_intervalMoments,
      `NK.FixedPointNat.enclose_mul,
      `NK.BinarySquares.odd_square_iff_mod_eight,
      `NK.BinaryGlue.glue_moment,
      `NK.retainedPair_fiber_card,
      `NK.RationalMomentCertificate.moment_bound,
      `NK.RationalPowerBounds.unitRpowBounds_sound,
      `NK.Certificates.fourth_power_bound,
      `NK.Certificates.sixth_power_bound,
      `NK.BinaryPolicy.Policy.exists_half_depth,
      `NK.BinaryCapacity.tendsto_capacity,
      `NK.PairCertificateTree.toAlphabet_moment,
      `NK.Certificates.binaryPolicy,
      `NK.Certificates.binary_depth_moment,
      `NK.Certificates.square_power_bound,
      `NK.Certificates.odd215_component,
      `NK.Certificates.odd437_component,
      `NK.closure_interval_lift,
      `NK.unitConductor_le_exponent_iff,
      `NK.unitPower_stabilizes,
      `NK.unitPower_stabilizes_block,
      `NK.LexicographicCapacity.capacity_lex,
      `NK.WordGraphCapacity.word_capacity,
      `NK.prime_power_capacity,
      `NK.IntervalAlphabet.moment_le_prime_power_capacity] do
    unless env.contains name do
      logError m!"Required development theorem missing: {name}"
  logInfo m!"Axiom audit checked {checked} NK declarations."
