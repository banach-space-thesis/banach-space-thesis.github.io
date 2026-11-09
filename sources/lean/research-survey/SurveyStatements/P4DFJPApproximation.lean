import SurveyStatements.P4DFJPFiniteRank
import SurveyStatements.P4DFJPContractionLimits
import SurveyStatements.P4Approximation

/-! Finite ambient projection ranges and strong approximation yield BAP
on the actual interpolation space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Filter Topology

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

namespace DFJPSpace

theorem hasBoundedApproximationProperty_of_contractions
    (D : DFJPGaugeData 𝕜 E) (T : ℕ → E →L[𝕜] E)
    (hK : ∀ n, ∀ x ∈ D.carrier, T n x ∈ D.carrier) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hpoint : ∀ x : E, Tendsto (fun n => T n x) atTop (𝓝 x))
    (F : ℕ → Submodule 𝕜 E) [∀ n, FiniteDimensional 𝕜 (F n)]
    (hF : ∀ n, ∀ x ∈ closure (Submodule.span 𝕜 D.carrier : Set E), T n x ∈ F n) :
    HasBoundedApproximationProperty 𝕜 (DFJPSpace D) := by
  apply HasSequentialBoundedApproximationProperty.boundedApproximation
  refine ⟨1, by norm_num, fun n => contraction D (T n) (hK n) (hT n), ?_, ?_, ?_⟩
  · intro n
    exact contraction_hasFiniteRank D (T n) (hK n) (hT n) (F n) (hF n)
  · intro n
    exact norm_contraction_le_one D (T n) (hK n) (hT n)
  · intro f
    exact tendsto_contractions D T hK hT hpoint f

theorem contraction_comp_of_eq (D : DFJPGaugeData 𝕜 E) (T S U : E →L[𝕜] E)
    (hKT : ∀ x ∈ D.carrier, T x ∈ D.carrier) (hT : ‖T‖ ≤ 1)
    (hKS : ∀ x ∈ D.carrier, S x ∈ D.carrier) (hS : ‖S‖ ≤ 1)
    (hKU : ∀ x ∈ D.carrier, U x ∈ D.carrier) (hU : ‖U‖ ≤ 1)
    (heq : T.comp S = U) :
    (contraction D T hKT hT).comp (contraction D S hKS hS) =
      contraction D U hKU hU := by
  apply ContinuousLinearMap.ext
  intro f
  apply inclusion_injective D
  change inclusion D (contractionLinearMap D T hKT hT
      (contractionLinearMap D S hKS hS f)) =
    inclusion D (contractionLinearMap D U hKU hU f)
  rw [inclusion_contractionLinearMap, inclusion_contractionLinearMap,
    inclusion_contractionLinearMap]
  exact congrArg (fun V : E →L[𝕜] E => V (inclusion D f)) heq

end DFJPSpace

end SurveyStatements.P4
