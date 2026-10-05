import ThesisCommon.Analysis.GowersMaureyCoding

/-! The two nontrivial norming terms, with their actual finite coefficient
bounds. These bounds make the implicit norm operator act on seminorms
between zero and the finite ℓ1 coefficient mass. -/
noncomputable section
open scoped BigOperators NNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem logarithmicWeight_nonneg (n : ℕ) : 0 ≤ logarithmicWeight n := by
  unfold logarithmicWeight
  apply div_nonneg
  · exact Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  · exact Real.log_nonneg (by norm_num)

theorem one_le_logarithmicWeight {n : ℕ} (hn : 0 < n) : 1 ≤ logarithmicWeight n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [logarithmicWeight, le_div_iff₀ hlog, one_mul]
  apply Real.log_le_log (by norm_num)
  exact_mod_cast (show 2 ≤ n + 1 by omega)

def inverseWeight (n : ℕ) : ℝ≥0 :=
  ⟨(logarithmicWeight n)⁻¹, inv_nonneg.mpr (logarithmicWeight_nonneg n)⟩

theorem inverseWeight_le_one {n : ℕ} (hn : 0 < n) :
    (inverseWeight n : ℝ) ≤ 1 := by
  exact inv_le_one_of_one_le₀ (one_le_logarithmicWeight hn)

/-- A sequence of successive finite intervals, with n ≥ 2 as printed. -/
structure IntervalTest where
  count : ℕ
  count_ge_two : 2 ≤ count
  interval : Fin count → Interval
  successive : ∀ i j, i < j → ∀ s ∈ (interval i).set, ∀ t ∈ (interval j).set, s < t

theorem IntervalTest.disjoint (T : IntervalTest) {i j : Fin T.count} (hij : i ≠ j) :
    Disjoint (T.interval i).set (T.interval j).set := by
  apply Finset.disjoint_left.mpr
  intro n hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (lt_irrefl n) (T.successive i j h n hi n hj)
  · exact (lt_irrefl n) (T.successive j i h n hj n hi)

def intervalAverage (p : Seminorm 𝕜 (C00 𝕜)) (T : IntervalTest) :
    Seminorm 𝕜 (C00 𝕜) :=
  inverseWeight T.count • ∑ i, p.comp (restrict (T.interval i))

theorem intervalAverage_apply (p : Seminorm 𝕜 (C00 𝕜)) (T : IntervalTest) (x : C00 𝕜) :
    intervalAverage p T x = (logarithmicWeight T.count)⁻¹ *
      ∑ i, p (restrict (T.interval i) x) := by
  change (logarithmicWeight T.count)⁻¹ *
    (∑ i, p.comp (restrict (T.interval i))) x = _
  congr 1
  have h := congrFun (map_sum (Seminorm.coeFnAddMonoidHom 𝕜 (C00 𝕜))
    (fun i : Fin T.count => p.comp (restrict (T.interval i))) Finset.univ) x
  simpa using h

theorem intervalAverage_le_mass (p : Seminorm 𝕜 (C00 𝕜)) (hp : p ≤ mass)
    (T : IntervalTest) : intervalAverage p T ≤ mass := by
  apply seminorm_le_mass
  intro n c
  rw [intervalAverage_apply]
  have hs : (∑ i, p (restrict (T.interval i) (Finsupp.single n c))) ≤ ‖c‖ := by
    by_cases hex : ∃ j, n ∈ (T.interval j).set
    · obtain ⟨j, hj⟩ := hex
      rw [Finset.sum_eq_single j]
      · simpa only [restrict_single, if_pos hj, mass_single] using
          hp (Finsupp.single n c)
      · intro i _ hij
        have hi : n ∉ (T.interval i).set := fun hi =>
          Finset.disjoint_left.mp (T.disjoint hij) hi hj
        simp [restrict_single, hi]
      · simp
    · have hn : ∀ j, n ∉ (T.interval j).set := fun j hj => hex ⟨j, hj⟩
      simp [restrict_single, hn]
  calc
    _ ≤ (inverseWeight T.count : ℝ) * ‖c‖ :=
      mul_le_mul_of_nonneg_left hs (inverseWeight T.count).property
    _ ≤ ‖c‖ := mul_le_of_le_one_left (norm_nonneg c)
      (inverseWeight_le_one (by have := T.count_ge_two; omega))

theorem intervalAverage_mono (T : IntervalTest) {p q : Seminorm 𝕜 (C00 𝕜)}
    (hpq : p ≤ q) : intervalAverage p T ≤ intervalAverage q T := by
  intro x
  change intervalAverage p T x ≤ intervalAverage q T x
  rw [intervalAverage_apply, intervalAverage_apply]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpq _)
    (inverseWeight T.count).property

theorem Successive.disjoint {k : ℕ} {g : Fin k → C00 𝕜} (hg : Successive g)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (g i).support (g j).support := by
  apply Finset.disjoint_left.mpr
  intro n hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (lt_irrefl n) (hg i j h n hi n hj)
  · exact (lt_irrefl n) (hg j i h n hj n hi)

theorem successive_sum_coordinate_norm_le {k : ℕ} {g : Fin k → C00 𝕜}
    (hg : Successive g) (hb : ∀ i n, ‖g i n‖ ≤ 1) (n : ℕ) :
    ‖(∑ i, g i) n‖ ≤ 1 := by
  classical
  rw [Finsupp.finset_sum_apply]
  by_cases hex : ∃ j, g j n ≠ 0
  · obtain ⟨j, hj⟩ := hex
    rw [Finset.sum_eq_single j]
    · exact hb j n
    · intro i _ hij
      by_contra hi
      exact Finset.disjoint_left.mp (hg.disjoint hij)
        (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hj)
    · simp
  · have hz : ∀ j, g j n = 0 := by simpa using hex
    simp [hz]

theorem specialFunctional_coordinate_norm_le {k : ℕ} (hk : 0 < k)
    {g : Fin k → C00 𝕜} (hg : Successive g)
    (hb : ∀ i n, ‖g i n‖ ≤ 1) (n : ℕ) : ‖specialFunctional g n‖ ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt (logarithmicWeight k) :=
    (Real.one_le_sqrt).mpr (one_le_logarithmicWeight hk)
  have hinv : (Real.sqrt (logarithmicWeight k))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hsqrt
  rw [specialFunctional, Finsupp.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (successive_sum_coordinate_norm_le hg hb n)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans (by simpa using hinv)

theorem specialEvaluation_le_mass (D : ConstructionData 𝕜)
    (p : Seminorm 𝕜 (C00 𝕜)) {k : ℕ} (hk : k ∈ D.specialSizes)
    {g : Fin k → C00 𝕜} (hg : SpecialSequence D p g) (E : Interval) :
    (evaluationSeminorm (specialFunctional g)).comp (restrict E) ≤ mass := by
  apply seminorm_le_mass
  intro n c
  change ‖pairing (specialFunctional g) (restrict E (Finsupp.single n c))‖ ≤ ‖c‖
  rw [restrict_single]
  split_ifs
  · rw [pairing_single, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg c)
      (specialFunctional_coordinate_norm_le (D.specialSize_pos hk) hg.1
        (fun i => (hg.2.1 i).2) n)
  · simp

end ThesisCommon.GowersMaurey
