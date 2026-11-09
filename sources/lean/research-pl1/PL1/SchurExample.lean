import PL1.L1Truncation
import PL1.CompactWalshMultiplier
import PL1.DyadicSchur
import PL1.NonSchurExample

/-!
# The concrete infinite-dimensional Schur projection

Unbounded coordinate rates give compact L-infinity restrictions of the
concrete convolution resolvents. The fully proved L1 restriction criterion
makes these resolvents Dunford-Pettis, and the dyadic construction gives an
actual Schur range and a Dunford-Pettis projection with the paper's bound.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace PL1.Noise

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The actual Haar L1 convolution resolvent is Dunford-Pettis whenever the
coordinate rates diverge. No analytic compactness hypothesis remains. -/
theorem resolventL1_isDunfordPettis_of_rates_tendsto (rates : ℕ → ℝ≥0)
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) (t : PositiveTime) :
    IsDunfordPettis (resolventL1 𝕜 rates t) :=
  L1Truncation.isDunfordPettis_of_compact_Linfty_restriction Walsh.haar _
    (WalshMultiplier.compact_resolventL1_restriction 𝕜 rates t hRateTop)

theorem schurRates_resolventL1_isDunfordPettis (t : PositiveTime) :
    IsDunfordPettis (resolventL1 𝕜 schurRates t) :=
  resolventL1_isDunfordPettis_of_rates_tendsto 𝕜 schurRates
    WalshMultiplier.tendsto_schurRates t

theorem intrinsic_hasSchurProperty_of_rates_tendsto (rates : ℕ → ℝ≥0)
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    HasSchurProperty 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace :=
  (dyadicSystem 𝕜 rates).hasSchurProperty_intrinsic
    (fun n => resolventL1_isDunfordPettis_of_rates_tendsto 𝕜 rates hRateTop (dyadicTime n))

theorem projection_range_hasSchurProperty_of_rates_tendsto (rates : ℕ → ℝ≥0)
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    HasSchurProperty 𝕜 (projection 𝕜 rates).range :=
  (dyadicSystem 𝕜 rates).hasSchurProperty_projection_range
    (fun n => resolventL1_isDunfordPettis_of_rates_tendsto 𝕜 rates hRateTop (dyadicTime n))

theorem projection_isDunfordPettis_of_rates_tendsto (rates : ℕ → ℝ≥0)
    (hRateTop : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    IsDunfordPettis (projection 𝕜 rates) :=
  (dyadicSystem 𝕜 rates).projection_isDunfordPettis
    (fun n => resolventL1_isDunfordPettis_of_rates_tendsto 𝕜 rates hRateTop (dyadicTime n))

theorem schurRates_intrinsic_hasSchurProperty :
    HasSchurProperty 𝕜 (dyadicSystem 𝕜 schurRates).IntrinsicSpace :=
  intrinsic_hasSchurProperty_of_rates_tendsto 𝕜 schurRates WalshMultiplier.tendsto_schurRates

theorem schurRates_projection_range_hasSchurProperty :
    HasSchurProperty 𝕜 (projection 𝕜 schurRates).range :=
  projection_range_hasSchurProperty_of_rates_tendsto 𝕜 schurRates WalshMultiplier.tendsto_schurRates

theorem schurRates_projection_isDunfordPettis :
    IsDunfordPettis (projection 𝕜 schurRates) :=
  projection_isDunfordPettis_of_rates_tendsto 𝕜 schurRates WalshMultiplier.tendsto_schurRates

/-- The completely concrete Schur projection on the countable sum of Haar L1
has infinite-dimensional closed range and the manuscript's quantitative bound. -/
theorem schurRates_projection_spec :
    IsProjection (projection 𝕜 schurRates) ∧
      ‖projection 𝕜 schurRates‖ ≤ projectionBound ∧
      IsClosed ((projection 𝕜 schurRates).range : Set (L1Sum (Lp 𝕜 1 Walsh.haar))) ∧
      ¬ FiniteDimensional 𝕜 (projection 𝕜 schurRates).range ∧
      HasSchurProperty 𝕜 (projection 𝕜 schurRates).range ∧
      IsDunfordPettis (projection 𝕜 schurRates) :=
  ⟨projection_isProjection 𝕜 schurRates, norm_projection_le 𝕜 schurRates,
    projection_range_isClosed 𝕜 schurRates, projection_range_infiniteDimensional 𝕜 schurRates,
    schurRates_projection_range_hasSchurProperty 𝕜, schurRates_projection_isDunfordPettis 𝕜⟩

end PL1.Noise
