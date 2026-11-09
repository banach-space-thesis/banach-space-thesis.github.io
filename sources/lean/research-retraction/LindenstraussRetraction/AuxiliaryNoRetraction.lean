import LindenstraussRetraction.RenormedRetractionObstruction
import LindenstraussRetraction.ConcreteConstruction
import LindenstraussRetraction.CoordinateRetractions
import LindenstraussRetraction.BidualLifting
import LindenstraussRetraction.NoSection
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The unit-ball obstruction for the explicitly constructed auxiliary sum -/

noncomputable section

open Filter Topology

namespace LindenstraussRetraction

universe v

variable (𝕜 : Type v) [RCLike 𝕜]

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem coordinateScale_le_half (n : ℕ) : coordinateScale n ≤ 1 / 2 := by
  rw [coordinateScale, pow_succ]
  calc
    (1 / 2 : ℝ) ^ n * (1 / 2) ≤ 1 * (1 / 2) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    _ = 1 / 2 := one_mul _

theorem coordinateScale_tendsto : Tendsto coordinateScale atTop (𝓝 0) := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp
    (tendsto_add_atTop_nat 1)

/-- Proposition `prop:auxiliary-space`: the closed unit ball of the actual
`W = (⊕Y_n)_{c₀}` admits no uniformly continuous retraction from its bidual
unit ball. All quotient, lifting, and no-section inputs are proved for the
concrete summation construction. -/
theorem no_uniformUnitBallRetraction_auxiliarySpace :
    ¬ HasUniformUnitBallBidualRetraction 𝕜 (AuxiliarySpace 𝕜) := by
  rintro ⟨R, hR, hfix⟩
  let E := RenormedSummationSpace 𝕜
  let C : FamilyCoordinates 𝕜 E (AuxiliarySpace 𝕜) := c0SumFamilyCoordinates 𝕜 E
  exact no_commonRenormedBallRetractions
    (summationOperator 𝕜) (summationOperator_isNormQuotient 𝕜)
    (no_uniformSection_summationOperator 𝕜)
    (summationBidualLift 𝕜) (fun x => (norm_summationBidualLift 𝕜 x).le)
    (summationBidualLift_rightInverse 𝕜)
    coordinateScale coordinateScale_pos coordinateScale_le_half coordinateScale_tendsto
    (coordinateRetraction 𝕜 E C R)
    (coordinateRetraction_uniformContinuous 𝕜 E C R hR)
    (coordinateRetraction_leftInverse 𝕜 E C R hfix)
    (coordinateRetraction_common_modulus 𝕜 E C R hR)

end LindenstraussRetraction
