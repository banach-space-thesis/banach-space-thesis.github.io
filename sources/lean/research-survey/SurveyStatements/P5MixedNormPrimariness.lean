import SurveyStatements.P5Assembly
import SurveyStatements.P5HaarDensity
import SurveyStatements.P5HaarCoordinates
import SurveyStatements.P5HaarMultipliers
import SurveyStatements.P5CompressionComposition
import SurveyStatements.P5HaarSubsequenceTrace
import SurveyStatements.P5VectorPartitionIndicators
import SurveyStatements.P5VectorPartitionNatural
import SurveyStatements.P5StableGeneratorLimit
import SurveyStatements.P5FaithfulMixedTrees
import SurveyStatements.P5VectorTensorLimits
import SurveyStatements.P5Support.LpHaarMultiplierStabilization
import SurveyStatements.P5L1VariationLinfty
import SurveyStatements.P5RademacherAverages
import SurveyStatements.P5RealScalarCapon
import SurveyStatements.P5BiTreeStabilization
import SurveyStatements.P5CaponGridRigidity
import SurveyStatements.P5FaithfulMixedCompression
import SurveyStatements.P5L1VariationOriginalLocalTrace
import SurveyStatements.P5GridScalarApproximation
import SurveyStatements.P5BiTreeGeometricBudget
import SurveyStatements.P5MultiplierScalarCompression
import SurveyStatements.P5OperatorReductionActualReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal

universe u
namespace SurveyStatements.P5
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean
variable (𝕜 : Type u) [RCLike 𝕜]

/-- For every finite exponent strictly greater than one, `Lp(L1)` has uniform
primary factorization and is primary. The `letI` supplies the standard Lp
normed-space instance from the explicit hypothesis `1 < p`.
The proof uses actual arbitrary-operator reduction and scalar multiplier
compression on the doubly cancellative space, followed by complemented-copy
transfer and the primariness consequence. -/
theorem mixed_norm_uniform_primary_factorization
    (p : ℝ≥0∞) (hp : 1 < p) (hp_finite : p < ∞) :
    letI : Fact (1 ≤ p) := ⟨le_of_lt hp⟩
    HasUniformPrimaryFactorization 𝕜 (MixedNorm 𝕜 p) ∧
      IsPrimary 𝕜 (MixedNorm 𝕜 p) := by
  letI : Fact (1 ≤ p) := ⟨le_of_lt hp⟩
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p) := inferInstance
  have hreduce : ∀ T : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
      ∀ δ : ℝ, 0 < δ →
      ∃ A B M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p,
        A.comp B = ContinuousLinearMap.id 𝕜 (DoublyZeroMean 𝕜 p) ∧
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        (∃ d : DyadicIndex → DyadicIndex → 𝕜, IsProductHaarMultiplier M d) ∧
        ‖(A.comp T).comp B - M‖ < δ := by
    intro T δ hδ
    let q : P5Support.BanachExponent := ⟨p, le_of_lt hp⟩
    have hOperators := P5OperatorReduction.arbitrary_operator_multiplier_compression
      q (ne_of_lt hp_finite) hp T hδ
    let A : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
      Classical.choose hOperators
    have hBExists := Classical.choose_spec hOperators
    let B : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
      Classical.choose hBExists
    have hMExists := Classical.choose_spec hBExists
    let M : DoublyZeroMean 𝕜 p →L[𝕜] DoublyZeroMean 𝕜 p :=
      Classical.choose hMExists
    have hdExists := Classical.choose_spec hMExists
    let d : DyadicIndex → DyadicIndex → 𝕜 := Classical.choose hdExists
    have hs := Classical.choose_spec hdExists
    exact ⟨A, B, M, hs.1, hs.2.1, hs.2.2.1, ⟨d, hs.2.2.2.1⟩, hs.2.2.2.2⟩
  have hscalar : HasScalarCompression 𝕜 (DoublyZeroMean 𝕜 p) :=
    scalarCompression_of_two_stage_reduction
      (fun M => ∃ d : DyadicIndex → DyadicIndex → 𝕜, IsProductHaarMultiplier M d)
      hreduce (by
        rintro M ⟨d, hd⟩ δ hδ
        exact productHaarMultiplier_scalar_compression (ne_of_lt hp_finite) M d hd δ hδ)
  have hfactor := mixedNorm_uniformPrimaryFactorization_of_scalarCompression
    𝕜 p (ne_of_lt hp_finite) hscalar
  exact ⟨hfactor, mixedNorm_primary_of_uniformPrimaryFactorization
    𝕜 p (ne_of_lt hp_finite) hfactor⟩

end SurveyStatements.P5

