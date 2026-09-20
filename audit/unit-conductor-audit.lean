import NK.UnitConductor

#print axioms NK.unitPower_stabilizes
#print axioms NK.unitPower_stabilizes_block
#print axioms NK.unitConductor_le_exponent_iff
#print axioms NK.binary_square_lookahead_counterexample
#print axioms NK.cyclic_power_image_preimage
#print axioms NK.binaryPrincipal_isCyclic

lemma conductor33 : NK.unitConductor 3 3 = 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  norm_num [NK.unitConductor, padicValNat_self]
example : NK.unitConductor 3 9 = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hv : padicValNat 3 9 = 2 := padicValNat.prime_pow 2
  norm_num [NK.unitConductor, hv]
lemma conductor24 : NK.unitConductor 2 4 = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 4 = 2 := padicValNat.prime_pow 2
  norm_num [NK.unitConductor, hv]
example : NK.unitConductor 2 6 = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 6 = 1 := by
    change padicValNat 2 (2 * 3) = 1
    rw [padicValNat.mul (by decide) (by decide), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  norm_num [NK.unitConductor, hv]
example : NK.unitConductor 2 3 = 1 := by decide

-- A singular odd prime: one digit falsely admits four as a cube; two reject it.
example : (1 : ℕ)^3 % 3 = 4 % 3 := by decide
example : ¬ ∃ z : Fin 9, z.val ^ 3 % 9 = 4 := by decide

-- Positive concrete lifting at a singular odd prime.
example : ∃ z : ℕ, z ^ 3 % 3 ^ 4 = 10 % 3 ^ 4 := by
  apply (NK.unitPower_stabilizes 3 3 10 4 (by decide) (by decide)
    (by decide) (by rw [conductor33]; decide)).mpr
  exact ⟨1, by rw [conductor33]; decide⟩

-- Binary fourth powers require the full four-bit conductor.
example : ∃ z : ℕ, z ^ 4 % 2 ^ 6 = 17 % 2 ^ 6 := by
  apply (NK.unitPower_stabilizes 2 4 17 6 (by decide) (by decide)
    (by decide) (by rw [conductor24]; decide)).mpr
  exact ⟨1, by rw [conductor24]; decide⟩
example : ¬ ∃ z : Fin 16, z.val ^ 4 % 16 = 9 := by decide

-- The unit hypothesis matters: three is zero mod three but no square mod nine.
example : (0 : ℕ)^2 % 3 = 3 % 3 := by decide
example : ¬ ∃ z : Fin 9, z.val ^ 2 % 9 = 3 := by decide
