import ThesisCommon.Analysis.IntegralDensityKernel
import ThesisCommon.Analysis.KernelSmallSetWitness

/-! Small output sets capturing an integral kernel's large-value mass on
a positive-measure input set. This is a witness statement, so the input
measure is nonzero and the threshold is positive. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace.CountablyGenerated Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
variable {k : X × Y → 𝕜} {C : ℝ}

theorem integral_norm_truncatedKernel_eq (hk : Measurable k) (r : ℝ) (x : X) :
    (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) =
      ∫ y in {y | r ≤ ‖k (x, y)‖}, ‖k (x, y)‖ ∂ν := by
  have hkx : Measurable (fun y => k (x, y)) := hk.comp measurable_prodMk_left
  rw [← integral_indicator (measurableSet_le measurable_const hkx.norm)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases h : r ≤ ‖k (x, y)‖ <;> simp [truncatedKernel, h]

theorem HasKernelBound.exists_smallSet_tail_witness_of_pos
    (hμ : μ ≠ 0) (hk : Measurable k) (hb : HasKernelBound μ ν k C)
    (hC : 0 < C) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ (B : Set Y) (M : Set X), MeasurableSet B ∧ ν.real B < 2 * C / r ∧
      MeasurableSet M ∧ 0 < μ M ∧
      ∀ x ∈ M, (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) - ε ≤
        ∫ y in B, ‖k (x, y)‖ ∂ν := by
  let A : Set (X × Y) := {z | r ≤ ‖k z‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const hk.norm
  have hsize : ∀ᵐ x ∂μ, ν.real (Prod.mk x ⁻¹' A) < 2 * C / r := by
    filter_upwards [hb] with x hx
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun y => norm_nonneg (k (x, y))) hx.1.norm r
    have hb' : ν.real (Prod.mk x ⁻¹' A) ≤ C / r := by
      apply (le_div_iff₀ hr).mpr
      change ν.real {y | r ≤ ‖k (x, y)‖} * r ≤ C
      nlinarith [hx.2]
    exact hb'.trans_lt ((div_lt_div_iff_of_pos_right hr).mpr (by linarith))
  let κ := boundedIntegralDensityKernel ν k C
  obtain ⟨B, M, hB, hBsize, hM, hMpos, hmass⟩ :=
    exists_smallSet_kernel_witness hμ κ A hA hε hsize
  obtain ⟨N, hNsup, hN, hN0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (hb.boundedIntegralDensityKernel_real_ae hk))
  refine ⟨B, M \ N, hB, hBsize, hM.diff hN, ?_, ?_⟩
  · rwa [measure_diff_null hN0]
  · intro x hx
    have hgood : ∀ D : Set Y, MeasurableSet D →
        (κ x).real D = ∫ y in D, ‖k (x, y)‖ ∂ν := by
      by_contra hn
      exact hx.2 (hNsup hn)
    have h := hmass x hx.1
    rw [hgood _ (measurable_prodMk_left hA), hgood B hB] at h
    rw [integral_norm_truncatedKernel_eq hk]
    change (∫ y in {y | r ≤ ‖k (x, y)‖}, ‖k (x, y)‖ ∂ν) ≤ _ at h
    linarith


/-- The non-strict size bound includes the zero kernel. -/
theorem HasKernelBound.exists_smallSet_tail_witness
    (hμ : μ ≠ 0) (hk : Measurable k) (hb : HasKernelBound μ ν k C)
    (hC : 0 ≤ C) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ (B : Set Y) (M : Set X), MeasurableSet B ∧ ν.real B ≤ 2 * C / r ∧
      MeasurableSet M ∧ 0 < μ M ∧
      ∀ x ∈ M, (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) - ε ≤
        ∫ y in B, ‖k (x, y)‖ ∂ν := by
  rcases hC.eq_or_lt with hC | hC
  · subst C
    have htail : ∀ᵐ x ∂μ, (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) ≤ 0 := by
      filter_upwards [hb, hb.truncatedKernel hk r] with x hx hxt
      exact (integral_mono hxt.1.norm hx.1.norm
        (fun y => norm_truncatedKernel_le r k (x, y))).trans hx.2
    obtain ⟨N, hNsup, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp htail)
    refine ⟨∅, univ \ N, MeasurableSet.empty, by simp, MeasurableSet.univ.diff hN, ?_, ?_⟩
    · rw [measure_diff_null hN0]
      exact bot_lt_iff_ne_bot.mpr (Measure.measure_univ_ne_zero.mpr hμ)
    · intro x hx
      have hx0 : (∫ y, ‖ThesisCommon.truncatedKernel r k (x, y)‖ ∂ν) ≤ 0 := by
        by_contra hn
        exact hx.2 (hNsup hn)
      simpa only [setIntegral_empty] using sub_nonpos.mpr (hx0.trans hε.le)
  · obtain ⟨B, M, hB, hsize, hM, hpos, hmass⟩ :=
      hb.exists_smallSet_tail_witness_of_pos hμ hk hC hr hε
    exact ⟨B, M, hB, hsize.le, hM, hpos, hmass⟩

end ThesisCommon
