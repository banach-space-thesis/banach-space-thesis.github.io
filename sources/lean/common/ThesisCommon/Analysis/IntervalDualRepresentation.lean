import ThesisCommon.Analysis.IntervalDualUpperRetraction
import ThesisCommon.Analysis.IntervalDualLowerRetraction
import ThesisCommon.Analysis.ComplementedSequenceDecomposition
import ThesisCommon.Analysis.LpArbitraryProducts

/-! The actual bounded dual of continuous interval functions is isomorphic
to the continuum-indexed ell-one sum of actual Lebesgue L1 spaces.
Both complemented embeddings are constructed from measures; the final
isomorphism is the proved decomposition method. No primariness input occurs. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace ThesisCommon

local instance intervalDualRepresentationDualGroup (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance intervalDualRepresentationDualSpace (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) := inferInstance
local instance intervalDualRepresentationSumGroup (𝕜 : Type*) [RCLike 𝕜] :
    NormedAddCommGroup (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance
local instance intervalDualRepresentationSumSpace (𝕜 : Type*) [RCLike 𝕜] :
    NormedSpace 𝕜 (EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) := inferInstance

def intervalContinuousDualLebesgueEquiv (𝕜 : Type*) [RCLike 𝕜] :
    (IntervalContinuous 𝕜 →L[𝕜] 𝕜) ≃L[𝕜]
      EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩) := Classical.choice (by
  letI : Infinite UnitInterval := Cardinal.aleph0_le_mk_iff.mp (by
    rw [Cardinal.mk_Icc_real (show (0 : ℝ) < 1 from zero_lt_one)]
    exact Cardinal.aleph0_le_continuum)
  obtain ⟨J, Q, _, hQJ⟩ := exists_intervalContinuousDual_upper_retraction 𝕜
  obtain ⟨I, R, _, _, hRI⟩ := exists_intervalContinuousDual_lower_retraction 𝕜
  let e := lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜)
    (X := IntervalLp 𝕜 ⟨1, le_rfl⟩) (Γ := UnitInterval) 1 (by norm_num)
  exact ⟨(lpDecompositionEquivOfRetractions 1 e.toContinuousLinearEquiv
    J.toContinuousLinearMap Q hQJ I R hRI).symm⟩)

theorem intervalContinuousDual_equiv_ellOneLebesgue (𝕜 : Type*) [RCLike 𝕜] :
    Nonempty ((IntervalContinuous 𝕜 →L[𝕜] 𝕜) ≃L[𝕜]
      EllOneSum UnitInterval (IntervalLp 𝕜 ⟨1, le_rfl⟩)) :=
  ⟨intervalContinuousDualLebesgueEquiv 𝕜⟩

end ThesisCommon
