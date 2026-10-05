import ThesisCommon.Analysis.GowersMaureyIntervalNorms

/-! The finite (k,g)-forms from Section 2, their interval-norm estimate,
and membership of the construction's averaged functionals in the dual ball. -/
noncomputable section
open scoped BigOperators NNReal
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The source's form, with g(k) supplied as a positive real weight. -/
def IsForm (D : ConstructionData 𝕜) (k : ℕ) (weight : ℝ) (a : C00 𝕜) : Prop :=
  DualUnit (implicitNorm D) a ∧ ∃ z : Fin k → C00 𝕜,
    Successive z ∧ (∀ i x, ‖pairing (z i) x‖ ≤ weight⁻¹ * implicitNorm D x) ∧
      a = ∑ i, z i

theorem successive_pairing_sum_le (D : ConstructionData 𝕜) {k : ℕ}
    {z : Fin k → C00 𝕜} (hz : Successive z) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ i x, ‖pairing (z i) x‖ ≤ c * implicitNorm D x) (x : C00 𝕜) :
    ‖pairing (∑ i, z i) x‖ ≤ c * intervalNorm D k x := by
  rw [pairing_sum_left]
  calc
    ‖∑ i, pairing (z i) x‖ ≤ ∑ i, ‖pairing (z i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i, c * implicitNorm D (restrict (supportInterval (z i)) x) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← pairing_restrict_supportInterval (z i) x]
      exact hb i _
    _ = c * intervalSum D (supportIntervalFamily z hz) x := by
      rw [intervalSum_apply, Finset.mul_sum]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (intervalSum_le_intervalNorm D _ x) hc

theorem IsForm.intervalNorm_bound {D : ConstructionData 𝕜} {k : ℕ}
    {weight : ℝ} (hw : 0 < weight) {a : C00 𝕜} (ha : IsForm D k weight a)
    (x : C00 𝕜) : ‖pairing a x‖ ≤ weight⁻¹ * intervalNorm D k x := by
  obtain ⟨_, z, hz, hb, rfl⟩ := ha
  exact successive_pairing_sum_le D hz (inv_nonneg.mpr hw.le) hb x

theorem successive_sum_coordinate_bound {k : ℕ} {z : Fin k → C00 𝕜}
    (hz : Successive z) {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i n, ‖z i n‖ ≤ c) (n : ℕ) :
    ‖(∑ i, z i) n‖ ≤ c := by
  classical
  rw [Finsupp.finset_sum_apply]
  by_cases hex : ∃ j, z j n ≠ 0
  · obtain ⟨j, hj⟩ := hex
    rw [Finset.sum_eq_single j]
    · exact hb j n
    · intro i _ hij
      by_contra hi
      exact Finset.disjoint_left.mp (hz.disjoint hij)
        (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hj)
    · simp
  · have hzero : ∀ j, z j n = 0 := by simpa using hex
    simpa [hzero] using hc

theorem IsForm.coordinate_bound {D : ConstructionData 𝕜} {k : ℕ}
    {weight : ℝ} (hw : 0 < weight) {a : C00 𝕜} (ha : IsForm D k weight a)
    (n : ℕ) : ‖a n‖ ≤ weight⁻¹ := by
  obtain ⟨_, z, hz, hb, rfl⟩ := ha
  apply successive_sum_coordinate_bound hz (inv_nonneg.mpr hw.le)
  intro i j
  simpa [implicitNorm_single] using hb i (Finsupp.single j 1)

theorem pairing_norm_le_mass {a : C00 𝕜} {c : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ c) (x : C00 𝕜) : ‖pairing a x‖ ≤ c * mass x := by
  classical
  conv_lhs => rw [← Finsupp.sum_single x]
  change ‖pairing a (∑ n ∈ x.support, Finsupp.single n (x n))‖ ≤ _
  rw [map_sum, mass_eq]
  simp only [pairing_single]
  calc
    ‖∑ n ∈ x.support, a n * x n‖ ≤ ∑ n ∈ x.support, ‖a n * x n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ x.support, c * ‖x n‖ := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)
    _ = c * ∑ n ∈ x.support, ‖x n‖ := (Finset.mul_sum _ _ _).symm

theorem IsForm.mass_bound {D : ConstructionData 𝕜} {k : ℕ}
    {weight : ℝ} (hw : 0 < weight) {a : C00 𝕜} (ha : IsForm D k weight a)
    (x : C00 𝕜) : ‖pairing a x‖ ≤ weight⁻¹ * mass x :=
  pairing_norm_le_mass (ha.coordinate_bound hw) x

theorem intervalNorm_lower_f (D : ConstructionData 𝕜) {k : ℕ} (hk : 0 < k)
    (x : C00 𝕜) : (logarithmicWeight k)⁻¹ * intervalNorm D k x ≤ implicitNorm D x := by
  by_cases hk1 : k = 1
  · subst k
    simp [intervalNorm_one, logarithmicWeight_one]
  · have hk2 : 2 ≤ k := by omega
    have hpos : 0 < logarithmicWeight k := lt_of_lt_of_le zero_lt_one (one_le_logarithmicWeight hk)
    rw [inv_mul_eq_div, div_le_iff₀ hpos]
    rw [intervalNorm, Seminorm.sSup_apply (intervalSums_bddAbove D k)]
    apply ciSup_le
    rintro ⟨_, I, rfl⟩
    change intervalSum D I x ≤ _
    rw [intervalSum_apply]
    have h := implicitNorm_intervalAverage_le D ⟨k, hk2, I.interval, I.successive⟩ x
    rw [inv_mul_eq_div] at h
    exact (div_le_iff₀ hpos).mp h

theorem AveragedFunctional.dualUnit {D : ConstructionData 𝕜} {k : ℕ} {a : C00 𝕜}
    (ha : AveragedFunctional (implicitNorm D) k a) : DualUnit (implicitNorm D) a := by
  obtain ⟨hk, z, hz, hb, rfl⟩ := ha
  intro x
  rw [pairing_real_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (logarithmicWeight_nonneg k))]
  have hs := successive_pairing_sum_le D hz (by norm_num : (0 : ℝ) ≤ 1)
    (fun i y => by simpa using hb i y) x
  have hinv : 0 ≤ (logarithmicWeight k)⁻¹ := inv_nonneg.mpr (logarithmicWeight_nonneg k)
  exact (mul_le_mul_of_nonneg_left (by simpa using hs) hinv).trans (intervalNorm_lower_f D hk x)

end ThesisCommon.GowersMaurey
