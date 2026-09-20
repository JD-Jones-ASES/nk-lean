import NK.BinaryPolicyGrowth

/-! Exact binary policy geometry, generated from the supplied mathematical witness.
Source: Naslund, commit e5d693729e23762b063a55015ad79ccaf28a3217.
Input SHA256: 2f43d95884dec55655dbd1f463fb4636831ef443b78248ca538e825c253721a7.
All containment, cyclic ordering, and seed bounds are proved below in Lean. -/
set_option maxHeartbeats 0
set_option maxRecDepth 32768
namespace NK.Certificates
open NK.BinaryPolicy

noncomputable def binaryState0 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

noncomputable def binaryState1 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState2 : State :=
  ![some ⟨(0 / 1 : ℝ), (13417006197 / 50000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(675896649089 / 1000000000000 : ℝ), (324103350911 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState3 : State :=
  ![some ⟨(0 / 1 : ℝ), (711431774821 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(97817985023 / 500000000000 : ℝ), (402182014977 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState4 : State :=
  ![some ⟨(0 / 1 : ℝ), (22243008731 / 31250000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(99324829091 / 500000000000 : ℝ), (400675170909 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState5 : State :=
  ![some ⟨(0 / 1 : ℝ), (42695319889 / 100000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(103831827471 / 200000000000 : ℝ), (96168172529 / 200000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState6 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(13417006197 / 50000000000 : ℝ), (407556525149 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState7 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(42695319889 / 100000000000 : ℝ), (18441187693 / 200000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState8 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

noncomputable def binaryState9 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

noncomputable def binaryState10 : State :=
  ![some ⟨(0 / 1 : ℝ), (27895001709 / 100000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(357241733771 / 500000000000 : ℝ), (142758266229 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState11 : State :=
  ![some ⟨(0 / 1 : ℝ), (339811267261 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState12 : State :=
  ![some ⟨(0 / 1 : ℝ), (198845711611 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(24863026581 / 50000000000 : ℝ), (25136973419 / 50000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState13 : State :=
  ![some ⟨(0 / 1 : ℝ), (96271277693 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4934953601 / 10000000000 : ℝ), (5065046399 / 10000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState14 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(27895001709 / 100000000000 : ℝ), (108883362613 / 250000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState15 : State :=
  ![some ⟨(0 / 1 : ℝ), (63360046137 / 200000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(192677593741 / 500000000000 : ℝ), (307322406259 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState16 : State :=
  ![some ⟨(0 / 1 : ℝ), (311683538613 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(47593989309 / 125000000000 : ℝ), (77406010691 / 125000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState17 : State :=
  ![some ⟨(0 / 1 : ℝ), (715163339539 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(12231691999 / 62500000000 : ℝ), (50268308001 / 62500000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState18 : State :=
  ![some ⟨(0 / 1 : ℝ), (4478275293 / 10000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(545858261303 / 1000000000000 : ℝ), (454141738697 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState19 : State :=
  ![some ⟨(0 / 1 : ℝ), (516867625413 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(189431939097 / 1000000000000 : ℝ), (810568060903 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState20 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(198845711611 / 1000000000000 : ℝ), (298414820009 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState21 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(63360046137 / 200000000000 : ℝ), (68554956797 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState22 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4478275293 / 10000000000 : ℝ), (98030732003 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState23 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(96271277693 / 500000000000 : ℝ), (150476402357 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryState24 : State :=
  ![some ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(311683538613 / 1000000000000 : ℝ), (69068375859 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩]

noncomputable def binaryWindows (i : Fin 25) : State :=
  match i.val with
  | 0 => binaryState0
  | 1 => binaryState1
  | 2 => binaryState2
  | 3 => binaryState3
  | 4 => binaryState4
  | 5 => binaryState5
  | 6 => binaryState6
  | 7 => binaryState7
  | 8 => binaryState8
  | 9 => binaryState9
  | 10 => binaryState10
  | 11 => binaryState11
  | 12 => binaryState12
  | 13 => binaryState13
  | 14 => binaryState14
  | 15 => binaryState15
  | 16 => binaryState16
  | 17 => binaryState17
  | 18 => binaryState18
  | 19 => binaryState19
  | 20 => binaryState20
  | 21 => binaryState21
  | 22 => binaryState22
  | 23 => binaryState23
  | 24 => binaryState24
  | _ => binaryState0

noncomputable def binaryRow0 : Row (Fin 25) :=
  ![some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none, some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none]

noncomputable def binaryClass0 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass0_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow0 c = binaryClass0 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow0, binaryClass0, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState1]

theorem binaryRow0_valid : RowValid binaryWindows binaryState0 binaryRow0 where
  inside := by
    intro c I hI
    rw [binaryClass0_exact] at hI
    fin_cases c <;> norm_num [binaryClass0] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState0, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass0_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass0] at hI hJ
    all_goals (cases hI <;> cases hJ)

noncomputable def binaryRow1 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (694268702473121 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨23, true, true, ⟨(0 / 1 : ℝ), (5482822151031929 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨19, false, false, ⟨(2213572781672638076731540203 / 5000000000000000000000000000 : ℝ), (5572854255910953 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(7307573741802039 / 10000000000000000 : ℝ), (1346213129098979 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass1 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (694268702473121 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(27770748592441706115473671 / 100000000000000000000000000 : ℝ), (825035352050552770957856653 / 5000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2213572781672638076731540203 / 5000000000000000000000000000 : ℝ), (2880427946025425296287848589 / 10000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(7307573741802039 / 10000000000000000 : ℝ), (1346213129098979 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (5482822151031929 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(5482822151347457054414309847 / 10000000000000000000000000000 : ℝ), (4517177667908772099048770559 / 10000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass1_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow1 c = binaryClass1 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow1, binaryClass1, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState19, binaryState23]

theorem binaryRow1_valid : RowValid binaryWindows binaryState1 binaryRow1 where
  inside := by
    intro c I hI
    rw [binaryClass1_exact] at hI
    fin_cases c <;> norm_num [binaryClass1] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState1, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass1_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass1] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow2 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (1341700569700881 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(675896649089 / 1000000000000 : ℝ), (3241033409109389 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (5366802278803523 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(675896649089 / 1000000000000 : ℝ), (6482066818218779 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass2 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (1341700569700881 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (5366802278803523 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(675896649089 / 1000000000000 : ℝ), (6482066818218779 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(675896649089 / 1000000000000 : ℝ), (3241033409109389 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass2_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow2 c = binaryClass2 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow2, binaryClass2, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow2_valid : RowValid binaryWindows binaryState2 binaryRow2 where
  inside := by
    intro c I hI
    rw [binaryClass2_exact] at hI
    fin_cases c <;> norm_num [binaryClass2] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState2, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass2_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass2] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow3 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (2962468172680721 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨6, true, true, ⟨(391271950407253684673466793 / 2000000000000000000000000000 : ℝ), (388035381687001 / 1250000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨3, true, true, ⟨(10569097770588113522089485271 / 25000000000000000000000000000 : ℝ), (14433392602049577 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(1309915895218763 / 2000000000000000 : ℝ), (690084104781237 / 2000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass3 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (2962468172680721 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2962468291850555689528997253 / 10000000000000000000000000000 : ℝ), (158146351795220037102888149 / 1250000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(10569097770588113522089485271 / 25000000000000000000000000000 : ℝ), (5804850919646423977910514729 / 25000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(1309915895218763 / 2000000000000000 : ℝ), (690084104781237 / 2000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(391271950407253684673466793 / 2000000000000000000000000000 : ℝ), (388035381687001 / 1250000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(1012128561106455284673466793 / 2000000000000000000000000000 : ℝ), (10268374115564421927342300717 / 50000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass3_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow3 c = binaryClass3 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow3, binaryClass3, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState3, binaryState6]

theorem binaryRow3_valid : RowValid binaryWindows binaryState3 binaryRow3 where
  inside := by
    intro c I hI
    rw [binaryClass3_exact] at hI
    fin_cases c <;> norm_num [binaryClass3] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState3, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass3_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass3] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow4 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(500000002265742488291049 / 50000000000000000000000000000000 : ℝ), (746849639670271 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨6, true, true, ⟨(19864966818195887 / 100000000000000000 : ℝ), (3088218747624669 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨3, true, true, ⟨(8492044859951476685367024937 / 20000000000000000000000000000 : ℝ), (5743480585601397 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(524475761989935049719170827 / 800000000000000000000000000 : ℝ), (275524238010064950280829173 / 800000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass4 : Fin 8 → Option UnitInterval :=
  ![some ⟨(500000002265742488291049 / 50000000000000000000000000000000 : ℝ), (746849639670271 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2987398726270915744627223459 / 10000000000000000000000000000 : ℝ), (1258623701681906695311300681 / 10000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(8492044859951476685367024937 / 20000000000000000000000000000 : ℝ), (2309924594898449778806122869 / 10000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(524475761989935049719170827 / 800000000000000000000000000 : ℝ), (275524238010064950280829173 / 800000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(19864966818195887 / 100000000000000000 : ℝ), (3088218747624669 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(50747154294442577 / 100000000000000000 : ℝ), (4086094586664358285367024937 / 20000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass4_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow4 c = binaryClass4 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow4, binaryClass4, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState3, binaryState6]

theorem binaryRow4_valid : RowValid binaryWindows binaryState4 binaryRow4 where
  inside := by
    intro c I hI
    rw [binaryClass4_exact] at hI
    fin_cases c <;> norm_num [binaryClass4] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState4, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass4_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass4] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow5 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (21347659444513897 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(103831827471 / 200000000000 : ℝ), (48084085264469483 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (42695318889027783 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(103831827471 / 200000000000 : ℝ), (4808408526446949 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass5 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (21347659444513897 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (42695318889027783 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(103831827471 / 200000000000 : ℝ), (4808408526446949 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(103831827471 / 200000000000 : ℝ), (48084085264469483 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass5_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow5 c = binaryClass5 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow5, binaryClass5, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow5_valid : RowValid binaryWindows binaryState5 binaryRow5 where
  inside := by
    intro c I hI
    rw [binaryClass5_exact] at hI
    fin_cases c <;> norm_num [binaryClass5] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState5, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass5_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass5] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow6 : Row (Fin 25) :=
  ![some ⟨2, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(13417006197 / 50000000000 : ℝ), (198266331187627 / 1250000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨7, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(10383182643268172529 / 20000000000000000000 : ℝ), (7836875086687797 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass6 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (1341700606282993803 / 5000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(13417006197 / 50000000000 : ℝ), (198266331187627 / 1250000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4269531946204680111 / 10000000000000000000 : ℝ), (1844118750858812307 / 20000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(10383182643268172529 / 20000000000000000000 : ℝ), (7836875086687797 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(67589664233003350911 / 100000000000000000000 : ℝ), (32410334766996649089 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass6_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow6 c = binaryClass6 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow6, binaryClass6, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState2, binaryState7]

theorem binaryRow6_valid : RowValid binaryWindows binaryState6 binaryRow6 where
  inside := by
    intro c I hI
    rw [binaryClass6_exact] at hI
    fin_cases c <;> norm_num [binaryClass6] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState6, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass6_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass6] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow7 : Row (Fin 25) :=
  ![some ⟨5, false, false, ⟨(0 / 1 : ℝ), (9999999899999999 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(42695320888997291 / 100000000000000000 : ℝ), (9220592846502709 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(42695319889 / 100000000000 : ℝ), (922059284650271 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass7 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (426953194620467968404680111 / 1000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(42695320888997291 / 100000000000000000 : ℝ), (9220592846502709 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(42695319889 / 100000000000 : ℝ), (922059284650271 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(1038318264326817149068172529 / 2000000000000000000000000000 : ℝ), (961681715673182650931827471 / 2000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass7_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow7 c = binaryClass7 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow7, binaryClass7, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState5]

theorem binaryRow7_valid : RowValid binaryWindows binaryState7 binaryRow7 where
  inside := by
    intro c I hI
    rw [binaryClass7_exact] at hI
    fin_cases c <;> norm_num [binaryClass7] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState7, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass7_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass7] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow8 : Row (Fin 25) :=
  ![some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none, some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none]

noncomputable def binaryClass8 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass8_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow8 c = binaryClass8 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow8, binaryClass8, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState1]

theorem binaryRow8_valid : RowValid binaryWindows binaryState8 binaryRow8 where
  inside := by
    intro c I hI
    rw [binaryClass8_exact] at hI
    fin_cases c <;> norm_num [binaryClass8] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState8, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass8_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass8] at hI hJ
    all_goals (cases hI <;> cases hJ)

noncomputable def binaryRow9 : Row (Fin 25) :=
  ![some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none, some ⟨1, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, none]

noncomputable def binaryClass9 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass9_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow9 c = binaryClass9 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow9, binaryClass9, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState1]

theorem binaryRow9_valid : RowValid binaryWindows binaryState9 binaryRow9 where
  inside := by
    intro c I hI
    rw [binaryClass9_exact] at hI
    fin_cases c <;> norm_num [binaryClass9] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState9, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass9_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass9] at hI hJ
    all_goals (cases hI <;> cases hJ)

noncomputable def binaryRow10 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (13947500354513567 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(357241733771 / 500000000000 : ℝ), (5710330449160723 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (13947500354513567 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(357241733771 / 500000000000 : ℝ), (2855165224580361 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass10 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (13947500354513567 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (13947500354513567 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(357241733771 / 500000000000 : ℝ), (2855165224580361 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(357241733771 / 500000000000 : ℝ), (5710330449160723 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass10_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow10 c = binaryClass10 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow10, binaryClass10, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow10_valid : RowValid binaryWindows binaryState10 binaryRow10 where
  inside := by
    intro c I hI
    rw [binaryClass10_exact] at hI
    fin_cases c <;> norm_num [binaryClass10] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState10, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass10_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass10] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow11 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (5697366819184283 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨20, true, true, ⟨(0 / 1 : ℝ), (11332643052382099 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨17, true, true, ⟨(18158391203383496031318047723 / 50000000000000000000000000000 : ℝ), (15822734665146057 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(1235380242246501 / 2000000000000000 : ℝ), (764619757753499 / 2000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass11 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (5697366819184283 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(284868347174743847194426481 / 1250000000000000000000000000 : ℝ), (3381828636702848431778618891 / 25000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(18158391203383496031318047723 / 50000000000000000000000000000 : ℝ), (795382099565661592926702057 / 3125000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(1235380242246501 / 2000000000000000 : ℝ), (764619757753499 / 2000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (11332643052382099 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(11332643052382099 / 25000000000000000 : ℝ), (11315839763765355031318047723 / 50000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass11_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow11 c = binaryClass11 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow11, binaryClass11, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState17, binaryState20]

theorem binaryRow11_valid : RowValid binaryWindows binaryState11 binaryRow11 where
  inside := by
    intro c I hI
    rw [binaryClass11_exact] at hI
    fin_cases c <;> norm_num [binaryClass11] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState11, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass11_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass11] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow12 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (4971142540279253 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(24863026581 / 50000000000 : ℝ), (2513697291901999 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (3976914032223403 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(24863026581 / 50000000000 : ℝ), (2513697291901999 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass12 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (4971142540279253 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (3976914032223403 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(24863026581 / 50000000000 : ℝ), (2513697291901999 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(24863026581 / 50000000000 : ℝ), (2513697291901999 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass12_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow12 c = binaryClass12 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow12, binaryClass12, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow12_valid : RowValid binaryWindows binaryState12 binaryRow12 where
  inside := by
    intro c I hI
    rw [binaryClass12_exact] at hI
    fin_cases c <;> norm_num [binaryClass12] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState12, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass12_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass12] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow13 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (962712726931801 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(4934953601 / 10000000000 : ℝ), (1266261574749019 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (19254254538636011 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(4934953601 / 10000000000 : ℝ), (202601851959843 / 400000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass13 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (962712726931801 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (19254254538636011 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4934953601 / 10000000000 : ℝ), (202601851959843 / 400000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(4934953601 / 10000000000 : ℝ), (1266261574749019 / 2500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass13_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow13 c = binaryClass13 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow13, binaryClass13, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow13_valid : RowValid binaryWindows binaryState13 binaryRow13 where
  inside := by
    intro c I hI
    rw [binaryClass13_exact] at hI
    fin_cases c <;> norm_num [binaryClass13] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState13, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass13_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass13] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow14 : Row (Fin 25) :=
  ![some ⟨10, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(27895001709 / 100000000000 : ℝ), (16887750220947603 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨22, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(54585825584441738697 / 100000000000000000000 : ℝ), (3372503924786429 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass14 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (2789500143004998291 / 10000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(27895001709 / 100000000000 : ℝ), (16887750220947603 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(447827524821724707 / 1000000000000000000 : ℝ), (9803073102269267997 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(54585825584441738697 / 100000000000000000000 : ℝ), (3372503924786429 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(35724173019858266229 / 50000000000000000000 : ℝ), (14275826480141733771 / 50000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass14_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow14 c = binaryClass14 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow14, binaryClass14, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState10, binaryState22]

theorem binaryRow14_valid : RowValid binaryWindows binaryState14 binaryRow14 where
  inside := by
    intro c I hI
    rw [binaryClass14_exact] at hI
    fin_cases c <;> norm_num [binaryClass14] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState14, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass14_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass14] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow15 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (39600027585571 / 125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(192677593741 / 500000000000 : ℝ), (9603825039347 / 15625000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (39600027585571 / 125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(192677593741 / 500000000000 : ℝ), (6146448025182081 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass15 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (39600027585571 / 125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (39600027585571 / 125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(192677593741 / 500000000000 : ℝ), (6146448025182081 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(192677593741 / 500000000000 : ℝ), (9603825039347 / 15625000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass15_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow15 c = binaryClass15 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow15, binaryClass15, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow15_valid : RowValid binaryWindows binaryState15 binaryRow15 where
  inside := by
    intro c I hI
    rw [binaryClass15_exact] at hI
    fin_cases c <;> norm_num [binaryClass15] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState15, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass15_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass15] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow16 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (31168352861265213 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(47593989309 / 125000000000 : ℝ), (123849615105537 / 200000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (1558417643063261 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(47593989309 / 125000000000 : ℝ), (387030047204803 / 625000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass16 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (31168352861265213 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (1558417643063261 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(47593989309 / 125000000000 : ℝ), (387030047204803 / 625000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(47593989309 / 125000000000 : ℝ), (123849615105537 / 200000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass16_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow16 c = binaryClass16 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow16, binaryClass16, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow16_valid : RowValid binaryWindows binaryState16 binaryRow16 where
  inside := by
    intro c I hI
    rw [binaryClass16_exact] at hI
    fin_cases c <;> norm_num [binaryClass16] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState16, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass16_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass16] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow17 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (29696419239571397 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨6, true, true, ⟨(391414154230910353314154869 / 2000000000000000000000000000 : ℝ), (15621116981030003 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨4, true, true, ⟨(4242939675994502372436307801 / 10000000000000000000000000000 : ℝ), (5817387199065811 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(262952891448961 / 400000000000000 : ℝ), (137047108551039 / 400000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass17 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (29696419239571397 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(7424105107148653412691127229 / 25000000000000000000000000000 : ℝ), (6366488155734625373593045447 / 50000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4242939675994502372436307801 / 10000000000000000000000000000 : ℝ), (2330882610229522627563692199 / 10000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(262952891448961 / 400000000000000 : ℝ), (137047108551039 / 400000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(391414154230910353314154869 / 2000000000000000000000000000 : ℝ), (15621116981030003 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(1016258833472110473314154869 / 2000000000000000000000000000 : ℝ), (129396194260428469116595841 / 625000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass17_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow17 c = binaryClass17 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow17, binaryClass17, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState4, binaryState6]

theorem binaryRow17_valid : RowValid binaryWindows binaryState17 binaryRow17 where
  inside := by
    intro c I hI
    rw [binaryClass17_exact] at hI
    fin_cases c <;> norm_num [binaryClass17] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState17, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass17_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass17] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow18 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (4478275192997473 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(545858261303 / 1000000000000 : ℝ), (2270708643486787 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(0 / 1 : ℝ), (22391375964987367 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(545858261303 / 1000000000000 : ℝ), (5676771608716967 / 12500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass18 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (4478275192997473 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (22391375964987367 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(545858261303 / 1000000000000 : ℝ), (5676771608716967 / 12500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(545858261303 / 1000000000000 : ℝ), (2270708643486787 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, none]

theorem binaryClass18_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow18 c = binaryClass18 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow18, binaryClass18, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0]

theorem binaryRow18_valid : RowValid binaryWindows binaryState18 binaryRow18 where
  inside := by
    intro c I hI
    rw [binaryClass18_exact] at hI
    fin_cases c <;> norm_num [binaryClass18] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState18, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass18_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass18] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow19 : Row (Fin 25) :=
  ![some ⟨0, false, false, ⟨(0 / 1 : ℝ), (2463166628264279 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨14, true, false, ⟨(9471597294641604826883170037 / 50000000000000000000000000000 : ℝ), (2039244576277139 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨11, true, true, ⟨(33513259984385077 / 100000000000000000 : ℝ), (18173501556929383 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(2584338077065723 / 5000000000000000 : ℝ), (2415661922934277 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass19 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (2463166628264279 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(12315833841657593490014697587 / 50000000000000000000000000000 : ℝ), (222039806655377263319204207 / 2500000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(33513259984385077 / 100000000000000000 : ℝ), (18173501556929383 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2584338077065723 / 5000000000000000 : ℝ), (2415661922934277 / 5000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(9471597294641604826883170037 / 50000000000000000000000000000 : ℝ), (2039244576277139 / 10000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(19667820176027299826883170037 / 50000000000000000000000000000 : ℝ), (6175560594629930173116829963 / 50000000000000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass19_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow19 c = binaryClass19 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow19, binaryClass19, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState11, binaryState14]

theorem binaryRow19_valid : RowValid binaryWindows binaryState19 binaryRow19 where
  inside := by
    intro c I hI
    rw [binaryClass19_exact] at hI
    fin_cases c <;> norm_num [binaryClass19] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState19, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass19_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass19] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow20 : Row (Fin 25) :=
  ![some ⟨12, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(198845711611 / 1000000000000 : ℝ), (471818036293591 / 4000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨21, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(19267759181422406259 / 50000000000000000000 : ℝ), (5595266706890423 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass20 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (19884570962254288389 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(198845711611 / 1000000000000 : ℝ), (471818036293591 / 4000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(6336004550339953863 / 20000000000000000000 : ℝ), (6855495611145043203 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(19267759181422406259 / 50000000000000000000 : ℝ), (5595266706890423 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2486302633236973419 / 5000000000000000000 : ℝ), (2513697316763026581 / 5000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass20_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow20 c = binaryClass20 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow20, binaryClass20, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState12, binaryState21]

theorem binaryRow20_valid : RowValid binaryWindows binaryState20 binaryRow20 where
  inside := by
    intro c I hI
    rw [binaryClass20_exact] at hI
    fin_cases c <;> norm_num [binaryClass20] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState20, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass20_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass20] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow21 : Row (Fin 25) :=
  ![some ⟨15, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨8, false, false, ⟨(3168002406845679 / 10000000000000000 : ℝ), (1371098935944479 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(63360046137 / 200000000000 : ℝ), (1371098935944481 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass21 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (6336004550339953863 / 20000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(3168002406845679 / 10000000000000000 : ℝ), (1371098935944479 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(63360046137 / 200000000000 : ℝ), (1371098935944481 / 20000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(19267759181422406259 / 50000000000000000000 : ℝ), (30732240318577593741 / 50000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass21_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow21 c = binaryClass21 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow21, binaryClass21, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState8, binaryState15]

theorem binaryRow21_valid : RowValid binaryWindows binaryState21 binaryRow21 where
  inside := by
    intro c I hI
    rw [binaryClass21_exact] at hI
    fin_cases c <;> norm_num [binaryClass21] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState21, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass21_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass21] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow22 : Row (Fin 25) :=
  ![some ⟨18, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(2239137696498737 / 5000000000000000 : ℝ), (1225384025036191 / 12500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(4478275293 / 10000000000 : ℝ), (2450768050072381 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass22 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (447827524821724707 / 1000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(2239137696498737 / 5000000000000000 : ℝ), (1225384025036191 / 12500000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(4478275293 / 10000000000 : ℝ), (2450768050072381 / 25000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(54585825584441738697 / 100000000000000000000 : ℝ), (45414173415558261303 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass22_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow22 c = binaryClass22 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow22, binaryClass22, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState18]

theorem binaryRow22_valid : RowValid binaryWindows binaryState22 binaryRow22 where
  inside := by
    intro c I hI
    rw [binaryClass22_exact] at hI
    fin_cases c <;> norm_num [binaryClass22] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState22, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass22_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass22] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow23 : Row (Fin 25) :=
  ![some ⟨13, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(96271277693 / 500000000000 : ℝ), (5957048661314603 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨24, true, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(4759398883306010691 / 12500000000000000000 : ℝ), (352323236337741 / 3125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass23 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (9627127673028722307 / 50000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(96271277693 / 500000000000 : ℝ), (5957048661314603 / 50000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(31168353549616461387 / 100000000000000000000 : ℝ), (6906837516831624141 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4759398883306010691 / 12500000000000000000 : ℝ), (352323236337741 / 3125000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(493495355165046399 / 1000000000000000000 : ℝ), (506504634834953601 / 1000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass23_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow23 c = binaryClass23 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow23, binaryClass23, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState13, binaryState24]

theorem binaryRow23_valid : RowValid binaryWindows binaryState23 binaryRow23 where
  inside := by
    intro c I hI
    rw [binaryClass23_exact] at hI
    fin_cases c <;> norm_num [binaryClass23] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState23, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass23_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass23] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRow24 : Row (Fin 25) :=
  ![some ⟨16, false, false, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(31168354861233703 / 100000000000000000 : ℝ), (6906836585966297 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨9, true, true, ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩, some ⟨0, false, false, ⟨(311683538613 / 1000000000000 : ℝ), (6906836585966301 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩⟩]

noncomputable def binaryClass24 : Fin 8 → Option UnitInterval :=
  ![some ⟨(0 / 1 : ℝ), (31168353549616461387 / 100000000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(31168354861233703 / 100000000000000000 : ℝ), (6906836585966297 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(311683538613 / 1000000000000 : ℝ), (6906836585966301 / 100000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, some ⟨(4759398883306010691 / 12500000000000000000 : ℝ), (7740600991693989309 / 12500000000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none, some ⟨(0 / 1 : ℝ), (99999999 / 100000000 : ℝ), by norm_num, by norm_num, by norm_num⟩, none]

theorem binaryClass24_exact (c : Fin 8) :
    classWindow binaryWindows binaryRow24 c = binaryClass24 c := by
  fin_cases c <;> norm_num [classWindow, classBranch, classParity, childWindows,
    binaryRow24, binaryClass24, binaryWindows, Transition.state, orientState,
    reflectState, swapState, BinaryPolicy.flip, affineState, UnitInterval.reflect, UnitInterval.comp,
    binaryState0, binaryState9, binaryState16]

theorem binaryRow24_valid : RowValid binaryWindows binaryState24 binaryRow24 where
  inside := by
    intro c I hI
    rw [binaryClass24_exact] at hI
    fin_cases c <;> norm_num [binaryClass24] at hI
    all_goals cases hI
    all_goals norm_num [InWindow, Contains, binaryState24, parity]
  cycle := by
    intro c d I J hI hJ hnext
    rw [binaryClass24_exact] at hI hJ
    have hd : d = (⟨(c.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) := Fin.ext hnext.symm
    subst d
    fin_cases c
    all_goals norm_num [binaryClass24] at hI hJ
    all_goals (cases hI <;> cases hJ <;> norm_num)

noncomputable def binaryRows (i : Fin 25) : Row (Fin 25) :=
  match i.val with
  | 0 => binaryRow0
  | 1 => binaryRow1
  | 2 => binaryRow2
  | 3 => binaryRow3
  | 4 => binaryRow4
  | 5 => binaryRow5
  | 6 => binaryRow6
  | 7 => binaryRow7
  | 8 => binaryRow8
  | 9 => binaryRow9
  | 10 => binaryRow10
  | 11 => binaryRow11
  | 12 => binaryRow12
  | 13 => binaryRow13
  | 14 => binaryRow14
  | 15 => binaryRow15
  | 16 => binaryRow16
  | 17 => binaryRow17
  | 18 => binaryRow18
  | 19 => binaryRow19
  | 20 => binaryRow20
  | 21 => binaryRow21
  | 22 => binaryRow22
  | 23 => binaryRow23
  | 24 => binaryRow24
  | _ => binaryRow0

theorem binaryRows_valid (i : Fin 25) : RowValid binaryWindows (binaryWindows i) (binaryRows i) := by
  fin_cases i
  · exact binaryRow0_valid
  · exact binaryRow1_valid
  · exact binaryRow2_valid
  · exact binaryRow3_valid
  · exact binaryRow4_valid
  · exact binaryRow5_valid
  · exact binaryRow6_valid
  · exact binaryRow7_valid
  · exact binaryRow8_valid
  · exact binaryRow9_valid
  · exact binaryRow10_valid
  · exact binaryRow11_valid
  · exact binaryRow12_valid
  · exact binaryRow13_valid
  · exact binaryRow14_valid
  · exact binaryRow15_valid
  · exact binaryRow16_valid
  · exact binaryRow17_valid
  · exact binaryRow18_valid
  · exact binaryRow19_valid
  · exact binaryRow20_valid
  · exact binaryRow21_valid
  · exact binaryRow22_valid
  · exact binaryRow23_valid
  · exact binaryRow24_valid

theorem binarySeeds_nonempty (i : Fin 25) : Nonempty (Seed (binaryWindows i)) := by
  fin_cases i
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState0], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState1], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(675896649089 / 1000000000000 : ℝ), (324103350911 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState2], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(97817985023 / 500000000000 : ℝ), (402182014977 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState3], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(99324829091 / 500000000000 : ℝ), (400675170909 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState4], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(103831827471 / 200000000000 : ℝ), (96168172529 / 200000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState5], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState6], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState7], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState8], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState9], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(357241733771 / 500000000000 : ℝ), (142758266229 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState10], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState11], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(24863026581 / 50000000000 : ℝ), (25136973419 / 50000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState12], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(4934953601 / 10000000000 : ℝ), (5065046399 / 10000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState13], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState14], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(192677593741 / 500000000000 : ℝ), (307322406259 / 500000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState15], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(47593989309 / 125000000000 : ℝ), (77406010691 / 125000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState16], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(12231691999 / 62500000000 : ℝ), (50268308001 / 62500000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState17], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(545858261303 / 1000000000000 : ℝ), (454141738697 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState18], by norm_num⟩⟩
  · exact ⟨⟨1, ⟨(189431939097 / 1000000000000 : ℝ), (810568060903 / 1000000000000 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState19], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState20], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState21], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState22], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState23], by norm_num⟩⟩
  · exact ⟨⟨0, ⟨(0 / 1 : ℝ), (1 / 1 : ℝ), by norm_num, by norm_num, by norm_num⟩,
      by norm_num [binaryWindows, binaryState24], by norm_num⟩⟩

noncomputable def binarySeeds (i : Fin 25) : Seed (binaryWindows i) :=
  Classical.choice (binarySeeds_nonempty i)

noncomputable def binaryPolicy : Policy (Fin 25) where
  windows := binaryWindows
  rows := binaryRows
  valid := binaryRows_valid
  seed := binarySeeds

end NK.Certificates
