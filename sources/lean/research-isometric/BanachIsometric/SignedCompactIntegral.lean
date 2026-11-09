import BanachIsometric.SignedArea
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Signed multiplicity integrals for compact Lipschitz sources

Boundedness of the derivative and continuity of determinant on a finite-
dimensional operator ball prove integrability. No integrability premise remains
in the signed formula for a compact source and a continuous target weight.
-/

namespace BanachIsometric

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_signedJacobian_mul_comp_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : IsCompact s)
    {g : E → ℝ} (hg : Continuous g) :
    IntegrableOn (fun x => (fderiv ℝ f x).det * g (f x)) s μ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hm : Measurable (fun x => (fderiv ℝ f x).det * g (f x)) :=
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)).mul
      (hg.comp hf.continuous).measurable
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) (K : ℝ)).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn (hg.comp hf.continuous).continuousOn
  apply IntegrableOn.of_bound hs.measure_lt_top hm.aestronglyMeasurable.restrict
    (max B 0 * max C 0)
  filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
  rw [norm_mul]
  have hDx : fderiv ℝ f x ∈ closedBall (0 : E →L[ℝ] E) (K : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact norm_fderiv_le_of_lipschitz ℝ hf
  exact mul_le_mul ((hB _ hDx).trans (le_max_left _ _))
    ((hC x hx).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

variable [Nontrivial E]

/-- The signed multiplicity integral formula on a compact Lipschitz source,
with integrability proved from the actual Lipschitz and compactness hypotheses.
This is an analytic area identity; degree constancy remains a separate step.
-/
theorem integral_signedRegularMultiplicity_of_compact_lipschitz
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : IsCompact s)
    {g : E → ℝ} (hg : Continuous g) :
    (∫ y, signedRegularMultiplicity f s y * g y ∂μ) =
      ∫ x in s, (fderiv ℝ f x).det * g (f x) ∂μ :=
  integral_signedRegularMultiplicity μ f hs.measurableSet g
    (integrableOn_signedJacobian_mul_comp_of_compact_lipschitz μ hf hs hg)

end BanachIsometric
