import ThesisCommon.Analysis.ComplexL1Coordinates
import ThesisCommon.Analysis.WeakCompactRestrictScalars
import ThesisCommon.Analysis.L1WeakUniformIntegrable
import ThesisCommon.Analysis.L1WeakUniformTight

/-! Necessary complex L1 small-set and tightness estimates, obtained from
genuine weak compactness through the full real and imaginary coordinate
maps. The domain is any complex normed space and the measure is arbitrary. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem norm_complexL1_le_coordinates (f : Lp ℂ 1 ν) :
    ‖f‖ ≤ ‖complexL1Re ν f‖ + ‖complexL1Im ν f‖ := by
  calc
    ‖f‖ = ‖complexL1OfReal ν (complexL1Re ν f) +
        Complex.I • complexL1OfReal ν (complexL1Im ν f)‖ := by rw [complexL1_decomposition]
    _ ≤ ‖complexL1OfReal ν (complexL1Re ν f)‖ +
        ‖Complex.I • complexL1OfReal ν (complexL1Im ν f)‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul, norm_complexL1OfReal, Complex.norm_I, one_mul]

theorem complexL1Re_cut (A : Set Y) (hA : MeasurableSet A) (f : Lp ℂ 1 ν) :
    complexL1Re ν (lpCut A hA f) = lpCut A hA (complexL1Re ν f) := by
  apply Lp.ext
  filter_upwards [complexL1Re_coe (lpCut A hA f), lpCut_coe A hA f,
    lpCut_coe A hA (complexL1Re ν f), complexL1Re_coe f] with y hr hc hc' hr'
  rw [hr, hc, hc']
  by_cases hy : y ∈ A <;> simp [hy, hr']

theorem complexL1Im_cut (A : Set Y) (hA : MeasurableSet A) (f : Lp ℂ 1 ν) :
    complexL1Im ν (lpCut A hA f) = lpCut A hA (complexL1Im ν f) := by
  apply Lp.ext
  filter_upwards [complexL1Im_coe (lpCut A hA f), lpCut_coe A hA f,
    lpCut_coe A hA (complexL1Im ν f), complexL1Im_coe f] with y hi hc hc' hi'
  rw [hi, hc, hc']
  by_cases hy : y ∈ A <;> simp [hy, hi']

theorem norm_lOneCut_comp_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] Lp ℝ 1 ν) {A B : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ‖(lpCutL A hA).comp T‖ ≤ ‖(lpCutL B hB).comp T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply le_trans (b := ‖lpCut B hB (T f)‖) _ (((lpCutL B hB).comp T).le_opNorm f)
  change ‖lpCut A hA (T f)‖ ≤ _
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpCut_coe A hA (T f), lpCut_coe B hB (T f)] with y hyA hyB
  rw [hyA, hyB]
  by_cases hy : y ∈ A
  · simp [hy, hAB hy]
  · simp [hy]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem norm_complexL1_cut_comp_le_coordinates
    (T : E →L[ℂ] Lp ℂ 1 ν) (A : Set Y) (hA : MeasurableSet A) :
    ‖(lpCutL A hA).comp T‖ ≤
      ‖(lpCutL A hA).comp ((complexL1Re ν).comp (T.restrictScalars ℝ))‖ +
      ‖(lpCutL A hA).comp ((complexL1Im ν).comp (T.restrictScalars ℝ))‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro f hf
  change ‖lpCut A hA (T f)‖ ≤ _
  have h := norm_complexL1_le_coordinates (lpCut A hA (T f))
  rw [complexL1Re_cut, complexL1Im_cut] at h
  exact h.trans (add_le_add
    (by simpa only [hf, mul_one] using
      ((lpCutL A hA).comp ((complexL1Re ν).comp (T.restrictScalars ℝ))).le_opNorm f)
    (by simpa only [hf, mul_one] using
      ((lpCutL A hA).comp ((complexL1Im ν).comp (T.restrictScalars ℝ))).le_opNorm f))

theorem IsWeaklyCompactOperator.exists_small_cut_norm_le_complex
    {T : E →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A, ∀ hA : MeasurableSet A,
      ν A ≤ ENNReal.ofReal δ → ‖(lpCutL A hA).comp T‖ ≤ ε := by
  obtain ⟨δ, hδ, hr⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Re ν)).exists_small_cut_norm_le (half_pos hε)
  obtain ⟨η, hη, hi⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Im ν)).exists_small_cut_norm_le (half_pos hε)
  refine ⟨min δ η, lt_min hδ hη, fun A hA hνA => ?_⟩
  have hreal := hr A hA (hνA.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have himag := hi A hA (hνA.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  exact (norm_complexL1_cut_comp_le_coordinates T A hA).trans
    (by linarith)

theorem IsWeaklyCompactOperator.exists_finite_measure_cut_compl_norm_le_complex
    {T : E →L[ℂ] Lp ℂ 1 ν} (hT : IsWeaklyCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Y, ∃ hA : MeasurableSet A, ν A < ∞ ∧ ‖(lpCutL Aᶜ hA.compl).comp T‖ ≤ ε := by
  obtain ⟨A, hA, hνA, hr⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Re ν)).exists_finite_measure_cut_compl_norm_le
      (half_pos hε)
  obtain ⟨B, hB, hνB, hi⟩ :=
    (hT.restrictScalars_real.comp_left (complexL1Im ν)).exists_finite_measure_cut_compl_norm_le
      (half_pos hε)
  refine ⟨A ∪ B, hA.union hB,
    (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hνA, hνB⟩), ?_⟩
  have hreal := (norm_lOneCut_comp_mono ((complexL1Re ν).comp (T.restrictScalars ℝ))
    (hA.union hB).compl hA.compl (compl_subset_compl.mpr subset_union_left)).trans hr
  have himag := (norm_lOneCut_comp_mono ((complexL1Im ν).comp (T.restrictScalars ℝ))
    (hA.union hB).compl hB.compl (compl_subset_compl.mpr subset_union_right)).trans hi
  exact (norm_complexL1_cut_comp_le_coordinates T (A ∪ B)ᶜ (hA.union hB).compl).trans
    (by linarith)

end ThesisCommon
