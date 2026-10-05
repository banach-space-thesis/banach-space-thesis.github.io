import PEMS.DeBlasiEllOneFactorization
import ThesisCommon.Analysis.ContinuousMapDualAL
import ThesisCommon.Analysis.ContinuousMapComplexDualAL

/-! De Blasi's measure equals the weak essential norm on intrinsic AL
spaces. In particular this proves the corresponding equality for actual
adjoints of C(K) operators, with different domain and range compacta. -/
noncomputable section
open ThesisCommon
namespace PEMS
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem deBlasiOperator_eq_weakEssentialNorm_real_AL
    [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (hE : IsALSpace ℝ E) (hF : IsALSpace ℝ F) :
    deBlasiOperator T = weakEssentialNorm T :=
  deBlasiOperator_eq_weakEssentialNorm_of_ellOne_factorization T
    (weakEssentialNorm_eq_factorizationSup_real_AL T hE hF)

theorem deBlasiOperator_eq_weakEssentialNorm_complex_AL
    [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]
    (T : E →L[ℂ] F) (hE : IsALSpace ℂ E) (hF : IsALSpace ℂ F) :
    deBlasiOperator T = weakEssentialNorm T :=
  deBlasiOperator_eq_weakEssentialNorm_of_ellOne_factorization T
    (weakEssentialNorm_eq_factorizationSup_complex_AL T hE hF)

variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem deBlasi_banachAdjoint_eq_dualWeakEssentialNorm_real_continuousMap
    (T : C(L, ℝ) →L[ℝ] C(K, ℝ)) :
    deBlasiOperator (banachAdjoint T) = dualWeakEssentialNorm T :=
  deBlasiOperator_eq_weakEssentialNorm_real_AL (banachAdjoint T)
    continuousMap_real_dual_isALSpace continuousMap_real_dual_isALSpace

theorem deBlasi_banachAdjoint_eq_dualWeakEssentialNorm_complex_continuousMap
    (T : C(L, ℂ) →L[ℂ] C(K, ℂ)) :
    deBlasiOperator (banachAdjoint T) = dualWeakEssentialNorm T :=
  deBlasiOperator_eq_weakEssentialNorm_complex_AL (banachAdjoint T)
    continuousMap_complex_dual_isALSpace continuousMap_complex_dual_isALSpace

end PEMS
