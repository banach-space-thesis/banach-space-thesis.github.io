import SurveyStatements.P5OperatorReductionPacketShadows
import SurveyStatements.P5OperatorReductionReaderAlgebra
import SurveyStatements.P5OperatorReductionMoments
import SurveyStatements.P5OperatorReductionPacketGeometryFunctions

/-! Actual raw Haar-packet shadows, using the full finite sign cube.
The packet families are arbitrary finite subsets of each dyadic level. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
variable {𝕜 ι : Type*} [RCLike 𝕜]

theorem rawPacketFunction_stronglyMeasurable (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜) :
    StronglyMeasurable (operatorReductionRawPacketFunction n S a) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  exact stronglyMeasurable_const.mul
    ((stronglyMeasurable_const.indicator measurableSet_Ioc).sub
      (stronglyMeasurable_const.indicator measurableSet_Ioc))

theorem norm_rawPacketFunction_le_one (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k ∈ S, ‖a k‖ ≤ 1) (x : ℝ) :
    ‖operatorReductionRawPacketFunction n S a x‖ ≤ 1 := by
  apply (norm_operatorReductionRawPacketFunction_le n S a ha x).trans
  by_cases hx : x ∈ lpHaarBlockParent n S <;> simp [hx]

theorem norm_scalarSign_eq_one (b : Bool) : ‖scalarSign (𝕜 := 𝕜) b‖ = 1 := by
  cases b <;> simp [scalarSign]

def rawHaarPacketShadow (p : BanachExponent)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 unitIntervalMeasure) : ι → Lp 𝕜 1 unitIntervalMeasure :=
  packetShadow (fun i => 2 ^ n i)
    (fun i θ => operatorReductionRawHaarPacket 𝕜 p (n i) (S i) (fun k => scalarSign (θ k)))
    (fun i θ => operatorReductionRawPacketFunction (n i) (S i) (fun k => scalarSign (θ k)))
    (fun i θ => rawPacketFunction_stronglyMeasurable (n i) (S i) (fun k => scalarSign (θ k)))
    (fun i θ => norm_rawPacketFunction_le_one (n i) (S i) (fun k => scalarSign (θ k))
      (fun k _ => (norm_scalarSign_eq_one (θ k)).le)) T g

theorem uniformSmallRestrictions_rawHaarPacketShadow (p : BanachExponent) (hp : p.val ≠ ∞)
    (n : ι → ℕ) (S : ∀ i, Finset (Fin (2 ^ n i)))
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    UniformSmallRestrictions (rawHaarPacketShadow p n S T g) := by
  apply uniformSmallRestrictions_packetShadow hp
  intro i θ
  filter_upwards [operatorReductionRawHaarPacket_ae (𝕜 := 𝕜) p (n i) (S i)
    (fun k => scalarSign (𝕜 := 𝕜) (θ k))] with x hx
  rw [hx]
  exact norm_rawPacketFunction_le_one (n i) (S i) (fun k => scalarSign (θ k))
    (fun k _ => (norm_scalarSign_eq_one (θ k)).le) x

end SurveyStatements.P5OperatorReduction
