import PEMS.ALBestApproximation
import PEMS.MainStatements
import ThesisCommon.Analysis.ContinuousMapAdjointApproximation
import ThesisCommon.Analysis.ContinuousMapDualAL
import ThesisCommon.Analysis.ContinuousMapComplexDualAL

/-! Corollary 1.2 for actual real and complex C(K) spaces. The AL structure
of the duals and the contractive bidual retraction of the range are constructed
in the common library; no representation or attainment premise is supplied. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem corollary_1_2_real (T : C(K, ℝ) →L[ℝ] C(L, ℝ)) :
    Corollary_1_2 K L T := by
  intro hL
  letI := hL
  obtain ⟨W, hW, he⟩ := exists_continuousMap_bestApproximation_of_adjoint_attainment T
    (exists_real_AL_weaklyCompact_bestApproximation (banachAdjoint T)
      (continuousMap_real_dual_isALSpace (K := L))
      (continuousMap_real_dual_isALSpace (K := K)))
  exact ⟨W, hW, weakEssentialNorm_banachAdjoint_eq_continuousMap T, he.symm⟩

theorem corollary_1_2_complex (T : C(K, ℂ) →L[ℂ] C(L, ℂ)) :
    Corollary_1_2 K L T := by
  intro hL
  letI := hL
  obtain ⟨W, hW, he⟩ := exists_continuousMap_bestApproximation_of_adjoint_attainment T
    (exists_complex_AL_weaklyCompact_bestApproximation (banachAdjoint T)
      (continuousMap_complex_dual_isALSpace (K := L))
      (continuousMap_complex_dual_isALSpace (K := K)))
  exact ⟨W, hW, weakEssentialNorm_banachAdjoint_eq_continuousMap T, he.symm⟩

end PEMS
