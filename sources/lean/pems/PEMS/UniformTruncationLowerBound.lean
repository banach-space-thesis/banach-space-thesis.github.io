import PEMS.SingularSmallSetSubset
import ThesisCommon.Analysis.IntegralKernelSmallSetSubset
import ThesisCommon.Analysis.IntegralKernelBandCuts

/-! The fixed-threshold lower estimate behind Proposition 4.17.
Its threshold depends only on the small-output-set tolerance and a common
kernel column bound, so it applies uniformly over uncountably many input pieces. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem positive_singular_kernel_tail_le_of_smallCuts
    (S K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hSing : IsSingularOperator S)
    {k : X × Y → ℝ} (hk : IsIntegralKernel k K) (hpos : ∀ z, 0 ≤ k z)
    (o : X → ℝ) (ho : Measurable o) {C δ r q : ℝ}
    (hC : 0 ≤ C) (hb : HasKernelBound μ ν k C) (hr : 0 < r) (hsize : 2 * C / r < δ)
    (hcuts : ∀ (B : Set Y) (hB : MeasurableSet B), ν.real B < δ →
      ∀ᵐ x ∂μ, o x + positiveAdjointOneDensity ((lpCutL B hB).comp (S + K))
        (positive_outputCut_nonneg (add_nonneg hS (hk.positive_of_nonneg_ae (Eventually.of_forall hpos))) B hB) x ≤ q) :
    ∀ᵐ x ∂μ, o x + positiveAdjointOneDensity S hS x +
      (∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν) ≤ q := by
  have hK : 0 ≤ K := hk.positive_of_nonneg_ae (Eventually.of_forall hpos)
  let a : X → ℝ := fun x => o x + positiveAdjointOneDensity S hS x +
    ∫ y, ‖truncatedKernel r k (x, y)‖ ∂ν
  have ha : Measurable a := (ho.add (measurable_positiveAdjointOneDensity S hS)).add
    (measurable_truncatedKernel hk.measurable r).stronglyMeasurable.norm.integral_prod_right'.measurable
  apply (ae_le_const_iff_forall_gt_measure_zero a q).mpr
  intro b hqb
  let M := {x | b ≤ a x}
  have hM : MeasurableSet M := measurableSet_le measurable_const ha
  by_contra hMzero
  have hμM : 0 < μ M := pos_iff_ne_zero.mpr hMzero
  let ε := (b - q) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨B, N, hB, hνB, hN, hNM, hμN, hsing⟩ :=
    singular_smallSet_preserves_adjoint_on_subset S hS hSing M hM hμM
      (δ := δ - 2 * C / r) (ε := ε) (sub_pos.mpr hsize) hε
  obtain ⟨G, P, hG, hνG, hP, hPN, hμP, hkernel⟩ :=
    hb.exists_smallSet_tail_witness_subset hk.measurable hC N hN hμN hr hε
  let H := B ∪ G
  have hH : MeasurableSet H := hB.union hG
  have hνBreal : ν.real B < δ - 2 * C / r := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top ν B) ENNReal.ofReal_ne_top).mpr hνB
    simpa only [measureReal_def, ENNReal.toReal_ofReal (sub_pos.mpr hsize).le] using hh
  have hνH : ν.real H < δ := (measureReal_union_le B G).trans_lt (by linarith)
  have hmono := positiveAdjointOneDensity_mono (positive_outputCut_nonneg hS B hB)
    (positive_outputCut_nonneg hS H hH) (positive_outputCut_mono_set hS hB hH subset_union_left)
  have hdens := positiveAdjointOneDensity_congr
    (positive_outputCut_nonneg (add_nonneg hS hK) H hH)
    (add_nonneg (positive_outputCut_nonneg hS H hH) (positive_outputCut_nonneg hK H hH))
    (ContinuousLinearMap.comp_add (lpCutL H hH) S K)
  have hadd := positiveAdjointOneDensity_add (positive_outputCut_nonneg hS H hH)
    (positive_outputCut_nonneg hK H hH)
  rw [← hdens] at hadd
  have hkH := hk.positiveAdjointOneDensity_outputCut hK H hH
  have hcut := hcuts H hH hνH
  letI : NeZero (μ.restrict P) := ⟨Measure.restrict_eq_zero.not.mpr hμP.ne'⟩
  have hall : ∀ᵐ x ∂μ.restrict P, x ∈ P ∧
      o x + positiveAdjointOneDensity ((lpCutL H hH).comp (S + K))
        (positive_outputCut_nonneg (add_nonneg hS hK) H hH) x ≤ q ∧
      positiveAdjointOneDensity ((lpCutL B hB).comp S) (positive_outputCut_nonneg hS B hB) x ≤
        positiveAdjointOneDensity ((lpCutL H hH).comp S) (positive_outputCut_nonneg hS H hH) x ∧
      positiveAdjointOneDensity ((lpCutL H hH).comp (S + K))
        (positive_outputCut_nonneg (add_nonneg hS hK) H hH) x =
        positiveAdjointOneDensity ((lpCutL H hH).comp S) (positive_outputCut_nonneg hS H hH) x +
        (∫ y in H, k (x, y) ∂ν) ∧ Integrable (fun y => k (x, y)) ν := by
    filter_upwards [ae_restrict_mem hP, ae_restrict_of_ae hcut, ae_restrict_of_ae hmono,
      ae_restrict_of_ae hadd, ae_restrict_of_ae hkH, ae_restrict_of_ae hb]
      with x hx hc hm ha hkx hbx
    exact ⟨hx, hc, hm, ha.trans (congrArg (_ + ·) hkx), hbx.1⟩
  obtain ⟨x, hxP, hcutx, hmonox, haddx, hix⟩ := hall.exists
  have hsingx := hsing x (hPN hxP)
  have hkx := hkernel x hxP
  have hGM : (∫ y in G, k (x, y) ∂ν) ≤ ∫ y in H, k (x, y) ∂ν :=
    setIntegral_mono_set hix.integrableOn (Eventually.of_forall fun y => hpos (x, y))
      (Eventually.of_forall fun _ hy => Or.inr hy)
  simp only [Real.norm_of_nonneg (hpos _)] at hkx
  have hax : b ≤ a x := hNM (hPN hxP)
  dsimp [a, ε] at hax hsingx hkx
  linarith

end PEMS
