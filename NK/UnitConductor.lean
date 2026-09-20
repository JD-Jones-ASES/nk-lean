import NK.PrimePowerUnits
import NK.BinarySquares
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! # Unit-power conductors and the binary square exception

The standard sufficient conductor is proved for every prime and every positive
exponent, including singular primes. Odd-prime unit groups and binary principal
unit groups are cyclic; stabilization follows from equality of power-image
indices. The final statements use natural modular roots. The conductor fits
inside a k-digit block except at binary squares, where a literal counterexample
exhibits the missing lookahead bit. No minimal-conductor assertion is made.
-/
namespace NK

/-- The standard sufficient precision for the local unit kth-power image. -/
def unitConductor (p k : ℕ) : ℕ :=
  if p = 2 then if Odd k then 1 else padicValNat 2 k + 2 else padicValNat p k + 1

/-- Conductors always have positive precision. -/
theorem unitConductor_pos (p k : ℕ) : 1 ≤ unitConductor p k := by
  unfold unitConductor
  split_ifs <;> omega

/-- A nonsingular prime needs only its first residue digit. -/
theorem unitConductor_eq_one_of_not_dvd (p k : ℕ) (hk : ¬ p ∣ k) :
    unitConductor p k = 1 := by
  by_cases hp2 : p = 2
  · subst p
    have hodd : Odd k := Nat.not_even_iff_odd.mp (fun he => hk he.two_dvd)
    simp [unitConductor, hodd]
  · simp [unitConductor, hp2, padicValNat.eq_zero_of_not_dvd hk]

/-- The conductor fits inside a k-digit block except at binary squares. -/
theorem unitConductor_le_exponent (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hexception : ¬ (p = 2 ∧ k = 2)) : unitConductor p k ≤ k := by
  by_cases hp2 : p = 2
  · subst p
    by_cases hodd : Odd k
    · simpa [unitConductor, hodd] using hk
    · have hkne : k ≠ 2 := by intro h; exact hexception ⟨rfl, h⟩
      have hk3 : 2 < k := by
        have hk1 : k ≠ 1 := by intro h; apply hodd; simp [h]
        omega
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hv := padicValNat_add_le_self (p := 2) hk3
      simpa [unitConductor, hodd] using hv
  · have hlog : Nat.log p k < k := Nat.log_lt_self p (by omega)
    have hv : padicValNat p k ≤ Nat.log p k := padicValNat_le_nat_log k
    simp only [unitConductor, if_neg hp2]
    omega

@[simp] theorem unitConductor_two_two : unitConductor 2 2 = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  norm_num [unitConductor, padicValNat_self]

/-- Binary squares are exactly the failure of the conductor-inside-block bound. -/
theorem unitConductor_le_exponent_iff (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    unitConductor p k ≤ k ↔ ¬ (p = 2 ∧ k = 2) := by
  constructor
  · intro h he
    rcases he with ⟨rfl, rfl⟩
    simp at h
  · exact unitConductor_le_exponent p k hp hk

/-- Complete stabilization for every nonsingular prime, at its defined conductor. -/
theorem unitPower_stabilizes_nonsingular (p k u n : ℕ) (hp : p.Prime)
    (hk : ¬ p ∣ k) (hu : ¬ p ∣ u) (hn : unitConductor p k ≤ n) :
    (∃ z : ℕ, z ^ k % p ^ n = u % p ^ n) ↔
      ∃ z : ℕ, z ^ k % p ^ unitConductor p k = u % p ^ unitConductor p k := by
  rw [unitConductor_eq_one_of_not_dvd p k hk] at hn ⊢
  simpa only [pow_one] using exists_pow_mod_prime_power_iff p k u n hp hk hu hn

/-- Binary squares stabilize at their three-bit conductor. -/
theorem unitPower_stabilizes_binary_squares (u n : ℕ) (hu : ¬ 2 ∣ u)
    (hn : unitConductor 2 2 ≤ n) :
    (∃ z : ℕ, z ^ 2 % 2 ^ n = u % 2 ^ n) ↔
      ∃ z : ℕ, z ^ 2 % 2 ^ unitConductor 2 2 = u % 2 ^ unitConductor 2 2 := by
  have huodd : u % 2 = 1 := by
    have hlt := Nat.mod_lt u (by decide : 0 < 2)
    have hne : u % 2 ≠ 0 := by intro h; exact hu (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [unitConductor_two_two] at hn ⊢
  simpa only [pow_two] using
    (BinarySquares.odd_square_iff_mod_eight n u hn huodd).trans
      (BinarySquares.odd_square_iff_mod_eight 3 u (by decide) huodd).symm

/-- Modulo four, five looks like a square; modulo sixteen it is not a square.
The missing bit is the precise binary-square lookahead obstruction. -/
theorem binary_square_lookahead_counterexample :
    (∃ z : ℕ, z ^ 2 % 4 = 5 % 4) ∧ ¬ (∃ z : ℕ, z ^ 2 % 16 = 5 % 16) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  intro h
  have hh : ∃ z : ℕ, (z * z) % 2 ^ 4 = 5 % 2 ^ 4 := by simpa [pow_two] using h
  have hbad := (BinarySquares.odd_square_iff_mod_eight 4 5 (by decide) (by decide)).mp hh
  norm_num at hbad

/-- For a surjection of finite cyclic groups, equal kth-power image indices
make the power image upstairs exactly the inverse image of the one downstairs. -/
theorem cyclic_power_image_preimage {G H : Type*} [CommGroup G] [CommGroup H]
    [Finite G] [Finite H] [IsCyclic G] [IsCyclic H]
    (f : G →* H) (hf : Function.Surjective f) (k : ℕ)
    (hindex : (Nat.card G).gcd k = (Nat.card H).gcd k) (a : G) :
    (∃ z : G, z ^ k = a) ↔ ∃ z : H, z ^ k = f a := by
  let U : Subgroup G := (powMonoidHom k : G →* G).range
  let V : Subgroup G := ((powMonoidHom k : H →* H).range).comap f
  have hle : U ≤ V := by
    rintro x ⟨z, rfl⟩
    exact ⟨f z, by simp⟩
  have hi : U.index = V.index := by
    dsimp only [U, V]
    rw [Subgroup.index_comap_of_surjective _ hf,
      IsCyclic.index_powMonoidHom_range, IsCyclic.index_powMonoidHom_range]
    exact hindex
  have heq : U = V := by
    rcases eq_or_lt_of_le hle with h | h
    · exact h
    · have hlt := Subgroup.index_strictAnti h
      omega
  have hmem : a ∈ U ↔ a ∈ V := by rw [heq]
  simpa only [U, V, Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply] using hmem

/-- Once the prime-power factor reaches the valuation of k, its contribution
to the gcd is stable, even after multiplying by any fixed factor. -/
theorem gcd_prime_power_mul_stable (p k c a b : ℕ) (hp : p.Prime) (hk : k ≠ 0)
    (hc : c ≠ 0) (ha : padicValNat p k ≤ a) (hb : padicValNat p k ≤ b) :
    (p ^ a * c).gcd k = (p ^ b * c).gcd k := by
  have hA : p ^ a * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hc
  have hB : p ^ b * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hc
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_right hk) (Nat.gcd_ne_zero_right hk)
  intro r
  rw [Nat.factorization_gcd hA hk, Nat.factorization_gcd hB hk,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hc,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hc,
    Nat.factorization_pow, Nat.factorization_pow]
  by_cases hr : r = p
  · subst r
    simp only [Finsupp.inf_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      hp.factorization_self, mul_one, Nat.factorization_def k hp]
    omega
  · have hpr : p.factorization r = 0 := by
      simp [hp.factorization, hr]
    simp only [Finsupp.inf_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hpr,
      mul_zero, zero_add]

/-- A unit residue has a natural modular kth root precisely when its unit-group
representative has a kth root. This bridge keeps the final statement elementary. -/
theorem nat_power_mod_iff_unit_power (m k u : ℕ) [NeZero m]
    (hk : 1 ≤ k) (hu : IsUnit (u : ZMod m)) :
    (∃ z : ℕ, z ^ k % m = u % m) ↔ ∃ z : (ZMod m)ˣ, z ^ k = hu.unit := by
  constructor
  · rintro ⟨z, hz⟩
    have he : (z : ZMod m) ^ k = (u : ZMod m) := by
      simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff' (z ^ k) u m).mpr hz
    have hzunit : IsUnit (z : ZMod m) :=
      (isUnit_pow_iff (by omega : k ≠ 0)).mp (he ▸ hu)
    refine ⟨hzunit.unit, Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using he
  · rintro ⟨z, hz⟩
    refine ⟨(z : ZMod m).val, (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_⟩
    have he := congrArg (fun a : (ZMod m)ˣ => (a : ZMod m)) hz
    simpa only [Nat.cast_pow, ZMod.natCast_zmod_val,
      Units.val_pow_eq_pow_val, IsUnit.unit_spec] using he

/-- All odd-prime unit kth-power images stabilize at valuation(k)+1, including
singular primes dividing k. The proof compares indices in finite cyclic groups. -/
theorem unitPower_stabilizes_odd_prime (p k u n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (hu : ¬ p ∣ u) (hn : unitConductor p k ≤ n) :
    (∃ z : ℕ, z ^ k % p ^ n = u % p ^ n) ↔
      ∃ z : ℕ, z ^ k % p ^ unitConductor p k = u % p ^ unitConductor p k := by
  let s := unitConductor p k
  have hs : s = padicValNat p k + 1 := by simp [s, unitConductor, hp2]
  have hspos : 0 < s := by omega
  have hnpos : 0 < n := by change s ≤ n at hn; omega
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  let : IsCyclic (ZMod (p ^ s))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 s
  have huN : IsUnit (u : ZMod (p ^ n)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hnpos).mpr hu
  have huS : IsUnit (u : ZMod (p ^ s)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hspos).mpr hu
  have hd : p ^ s ∣ p ^ n := pow_dvd_pow p hn
  have hindex : (Nat.card (ZMod (p ^ n))ˣ).gcd k =
      (Nat.card (ZMod (p ^ s))ˣ).gcd k := by
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp hnpos, Nat.totient_prime_pow hp hspos]
    apply gcd_prime_power_mul_stable p k (p - 1) (n - 1) (s - 1) hp (by omega)
      (by have := hp.two_le; omega)
    · change s ≤ n at hn
      omega
    · omega
  have hmap : ZMod.unitsMap hd huN.unit = huS.unit := by
    apply Units.ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, IsUnit.unit_spec]
    exact ZMod.cast_natCast hd u
  rw [nat_power_mod_iff_unit_power _ _ _ hk huN,
    nat_power_mod_iff_unit_power _ _ _ hk huS]
  rw [← hmap]
  exact cyclic_power_image_preimage (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) k hindex _

/-- The principal binary units, indexed so that n=0 means modulus four. -/
def binaryPrincipal (n : ℕ) : Subgroup (ZMod (2 ^ (n + 2)))ˣ :=
  (ZMod.unitsMap (show 4 ∣ 2 ^ (n + 2) by
    simpa using Nat.pow_dvd_pow 2 (show 2 ≤ n + 2 by omega))).ker

/-- Precisely half of the odd residues are one modulo four. -/
theorem binaryPrincipal_card (n : ℕ) : Nat.card (binaryPrincipal n) = 2 ^ n := by
  have hd : 4 ∣ 2 ^ (n + 2) := by
    simpa using Nat.pow_dvd_pow 2 (show 2 ≤ n + 2 by omega)
  have hi : (binaryPrincipal n).index = 2 := by
    change (ZMod.unitsMap hd).ker.index = 2
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hd), Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  have htot : (2 ^ (n + 2)).totient = 2 ^ n * 2 := by
    simpa only [Nat.reduceSub, mul_one, pow_succ] using
      Nat.totient_prime_pow_succ Nat.prime_two (n + 1)
  have hc := (binaryPrincipal n).card_mul_index
  rw [hi, Nat.card_eq_fintype_card (α := (ZMod (2 ^ (n + 2)))ˣ),
    ZMod.card_units_eq_totient, htot] at hc
  omega

/-- Five generates the entire principal binary unit subgroup. -/
theorem binaryPrincipal_isCyclic (n : ℕ) : IsCyclic (binaryPrincipal n) := by
  have hu : IsUnit (5 : ZMod (2 ^ (n + 2))) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega)).mpr (by decide)
  have hm : hu.unit ∈ binaryPrincipal n := by
    change ZMod.unitsMap _ hu.unit = 1
    apply Units.ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec]
    change (ZMod.cast (5 : ZMod (2 ^ (n + 2))) : ZMod 4) = 1
    exact (ZMod.cast_natCast
      (show 4 ∣ 2 ^ (n + 2) by
        simpa using Nat.pow_dvd_pow 2 (show 2 ≤ n + 2 by omega)) 5).trans (by decide)
  apply isCyclic_of_orderOf_eq_card (⟨hu.unit, hm⟩ : binaryPrincipal n)
  rw [Subgroup.orderOf_mk, ← orderOf_injective _ Units.coeHom_injective hu.unit,
    Units.coeHom_apply, IsUnit.unit_spec, ZMod.orderOf_five, binaryPrincipal_card]

/-- Reduction preserves the principal binary unit subgroups. -/
def binaryPrincipalMap (a b : ℕ) (hab : a ≤ b) :
    binaryPrincipal b →* binaryPrincipal a where
  toFun z := ⟨ZMod.unitsMap (Nat.pow_dvd_pow 2 (Nat.add_le_add_right hab 2)) z.val, by
    change ZMod.unitsMap _ (ZMod.unitsMap _ z.val) = 1
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    exact z.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

/-- Reduction is surjective on principal units; lifting a residue cannot change
its reduction modulo four. -/
theorem binaryPrincipalMap_surjective (a b : ℕ) (hab : a ≤ b) :
    Function.Surjective (binaryPrincipalMap a b hab) := by
  intro x
  have hd := Nat.pow_dvd_pow 2 (Nat.add_le_add_right hab 2)
  obtain ⟨z, hz⟩ := ZMod.unitsMap_surjective hd x.val
  have hzmem : z ∈ binaryPrincipal b := by
    have hx := x.property
    change ZMod.unitsMap _ x.val = 1 at hx
    rw [← hz, ← MonoidHom.comp_apply, ZMod.unitsMap_comp] at hx
    exact hx
  exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

/-- Changing an odd root's sign puts it into the principal unit subgroup and
preserves every even power. -/
theorem exists_principal_same_even_power (n k : ℕ) (hk : Even k)
    (z : (ZMod (2 ^ (n + 2)))ˣ) :
    ∃ w : binaryPrincipal n, (w.val) ^ k = z ^ k := by
  have hcases : ∀ x : (ZMod 4)ˣ, x = 1 ∨ x = -1 := by decide
  rcases hcases (ZMod.unitsMap
    (show 4 ∣ 2 ^ (n + 2) by
      simpa using Nat.pow_dvd_pow 2 (show 2 ≤ n + 2 by omega)) z) with h | h
  · exact ⟨⟨z, h⟩, rfl⟩
  · have hm : -z ∈ binaryPrincipal n := by
      change ZMod.unitsMap _ (-z) = 1
      rw [ZMod.unitsMap_def, Units.map_neg]
      change -(ZMod.unitsMap _ z) = 1
      rw [h, neg_neg]
    exact ⟨⟨-z, hm⟩, hk.neg_pow z⟩

/-- Even-power images are preserved and reflected by binary unit reduction
once both principal-unit orders reach the valuation of the exponent. -/
theorem binary_even_power_image_preimage (a b k : ℕ) (hab : a ≤ b)
    (hk : 1 ≤ k) (heven : Even k) (hka : padicValNat 2 k ≤ a)
    (u : (ZMod (2 ^ (b + 2)))ˣ) :
    (∃ z : (ZMod (2 ^ (b + 2)))ˣ, z ^ k = u) ↔
      ∃ z : (ZMod (2 ^ (a + 2)))ˣ,
        z ^ k = ZMod.unitsMap (Nat.pow_dvd_pow 2 (Nat.add_le_add_right hab 2)) u := by
  let hd := Nat.pow_dvd_pow 2 (Nat.add_le_add_right hab 2)
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨ZMod.unitsMap hd z, by simp⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := exists_principal_same_even_power a k heven z
    have hwroot : w.val ^ k = ZMod.unitsMap hd u := hw.trans hz
    have humem : u ∈ binaryPrincipal b := by
      have h4 : 4 ∣ 2 ^ (a + 2) := by
        simpa using Nat.pow_dvd_pow 2 (show 2 ≤ a + 2 by omega)
      have hr : ZMod.unitsMap h4 (ZMod.unitsMap hd u) = 1 := by
        rw [← hwroot, map_pow]
        rw [show ZMod.unitsMap h4 w.val = 1 from w.property, one_pow]
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp] at hr
      exact hr
    let uB : binaryPrincipal b := ⟨u, humem⟩
    have hrootA : ∃ v : binaryPrincipal a,
        v ^ k = binaryPrincipalMap a b hab uB := by
      refine ⟨w, Subtype.ext ?_⟩
      exact hwroot
    let : IsCyclic (binaryPrincipal a) := binaryPrincipal_isCyclic a
    let : IsCyclic (binaryPrincipal b) := binaryPrincipal_isCyclic b
    have hindex : (Nat.card (binaryPrincipal b)).gcd k =
        (Nat.card (binaryPrincipal a)).gcd k := by
      rw [binaryPrincipal_card, binaryPrincipal_card]
      simpa only [mul_one] using gcd_prime_power_mul_stable 2 k 1 b a Nat.prime_two
        (by omega) one_ne_zero (hka.trans hab) hka
    obtain ⟨v, hv⟩ := (cyclic_power_image_preimage (binaryPrincipalMap a b hab)
      (binaryPrincipalMap_surjective a b hab) k hindex uB).mpr hrootA
    exact ⟨v.val, congrArg Subtype.val hv⟩

/-- Every even binary exponent stabilizes at valuation₂(k)+2. -/
theorem unitPower_stabilizes_binary_even (k u n : ℕ) (hk : 1 ≤ k)
    (heven : Even k) (hu : ¬ 2 ∣ u) (hn : unitConductor 2 k ≤ n) :
    (∃ z : ℕ, z ^ k % 2 ^ n = u % 2 ^ n) ↔
      ∃ z : ℕ, z ^ k % 2 ^ unitConductor 2 k = u % 2 ^ unitConductor 2 k := by
  have hs : unitConductor 2 k = padicValNat 2 k + 2 := by
    simp [unitConductor, Nat.not_odd_iff_even.mpr heven]
  rw [hs] at hn ⊢
  have hn2 : n = (n - 2) + 2 := by omega
  rw [hn2]
  have hab : padicValNat 2 k ≤ n - 2 := by omega
  have huN : IsUnit (u : ZMod (2 ^ ((n - 2) + 2))) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega)).mpr hu
  have huS : IsUnit (u : ZMod (2 ^ (padicValNat 2 k + 2))) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega)).mpr hu
  have hd := Nat.pow_dvd_pow 2 (Nat.add_le_add_right hab 2)
  have hmap : ZMod.unitsMap hd huN.unit = huS.unit := by
    apply Units.ext
    rw [ZMod.unitsMap_val, IsUnit.unit_spec, IsUnit.unit_spec]
    exact ZMod.cast_natCast hd u
  rw [nat_power_mod_iff_unit_power _ _ _ hk huN,
    nat_power_mod_iff_unit_power _ _ _ hk huS, ← hmap]
  exact binary_even_power_image_preimage (padicValNat 2 k) (n - 2) k hab hk heven le_rfl _

/-- Full unit-power conductor theorem, for every prime and every positive
exponent. Roots are ordinary natural numbers and no root-lifting premise is used. -/
theorem unitPower_stabilizes (p k u n : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hu : ¬ p ∣ u) (hn : unitConductor p k ≤ n) :
    (∃ z : ℕ, z ^ k % p ^ n = u % p ^ n) ↔
      ∃ z : ℕ, z ^ k % p ^ unitConductor p k = u % p ^ unitConductor p k := by
  by_cases hp2 : p = 2
  · subst p
    by_cases hd : 2 ∣ k
    · exact unitPower_stabilizes_binary_even k u n hk (even_iff_two_dvd.mpr hd) hu hn
    · exact unitPower_stabilizes_nonsingular 2 k u n hp hd hu hn
  · exact unitPower_stabilizes_odd_prime p k u n hp hp2 hk hu hn

/-- Outside binary squares, one base-p^k block contains all unit-power data. -/
theorem unitPower_stabilizes_block (p k u n : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hu : ¬ p ∣ u) (hexception : ¬ (p = 2 ∧ k = 2)) (hn : k ≤ n) :
    (∃ z : ℕ, z ^ k % p ^ n = u % p ^ n) ↔ ∃ z : ℕ, z ^ k % p ^ k = u % p ^ k := by
  have hs := unitConductor_le_exponent p k hp hk hexception
  exact (unitPower_stabilizes p k u n hp hk hu (hs.trans hn)).trans
    (unitPower_stabilizes p k u k hp hk hu hs).symm

end NK
