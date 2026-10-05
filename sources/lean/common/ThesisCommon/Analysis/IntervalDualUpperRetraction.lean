import ThesisCommon.Analysis.ContinuousMapDualBoundedMeasureFamily
import ThesisCommon.Analysis.IntervalFiniteMeasureL1Embedding
import ThesisCommon.Analysis.LpFamilyContractiveRetractions

/-! The actual interval dual embeds isometrically and contractively
complementedly into the continuum-indexed ell-one sum of Lebesgue L1.
The maps use the proved measure family, finite-measure sampling retractions,
and an actual injection of its index set into the interval. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open MeasureTheory
namespace ThesisCommon

local instance intervalDualUpperDualGroup (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance intervalDualUpperDualSpace (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance intervalDualUpperSumGroup (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance
local instance intervalDualUpperSumSpace (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance

theorem exists_intervalContinuousDual_upper_retraction (𝕜 : Type*) [RCLike 𝕜] :
    ∃ (J : (IntervalContinuous 𝕜 →L[𝕜] 𝕜) →ₗᵢ[𝕜]
          EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩))
      (R : EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩) →L[𝕜]
          (IntervalContinuous 𝕜 →L[𝕜] 𝕜)),
      ‖R‖ ≤ 1 ∧ R.comp J.toContinuousLinearMap =
        ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := by
  obtain ⟨I, μ, hI, hμ, ⟨d⟩⟩ := exists_intervalContinuousDual_bounded_measure_family 𝕜
  letI (i : I) : IsFiniteMeasure (μ i) := hμ i
  have hi : Cardinal.mk I ≤ Cardinal.mk UnitInterval := by
    have hcard : Cardinal.mk UnitInterval = Cardinal.continuum :=
      Cardinal.mk_Icc_real (show (0 : ℝ) < 1 from zero_lt_one)
    rwa [hcard]
  obtain ⟨e⟩ := (Cardinal.le_def I UnitInterval).mp hi
  choose J R hR hRJ using fun i => exists_intervalFiniteMeasureL1_retraction 𝕜 (μ i)
  obtain ⟨A, B, hB, hBA⟩ := lpFamily_exists_contractive_retraction 1 e J R hR hRJ
  let F := A.comp d.toLinearIsometry
  let G := d.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B
  refine ⟨F, G, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖d.symm (B x)‖ ≤ 1 * ‖x‖
    rw [d.symm.norm_map, one_mul]
    exact (B.le_opNorm x).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (norm_nonneg x))
  · apply ContinuousLinearMap.ext
    intro x
    change d.symm (B (A (d x))) = x
    have hh := DFunLike.congr_fun hBA (d x)
    change B (A (d x)) = d x at hh
    rw [hh, d.symm_apply_apply]

end ThesisCommon
