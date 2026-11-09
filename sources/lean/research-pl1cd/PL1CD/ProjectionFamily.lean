import PL1CD.Statements
import PL1.ConcreteResolvents
import PL1.NonSchurExample
import PL1.IntervalWalsh
import PL1.SchurExample

noncomputable section
open Filter
open scoped NNReal

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

def intervalProjection (rates : ℕ → ℝ≥0) : L1Operator 𝕜 :=
  (PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).transport
    (PL1.Noise.projection 𝕜 rates)

theorem intervalProjection_isProjection (rates : ℕ → ℝ≥0) :
    PL1.IsProjection (intervalProjection 𝕜 rates) :=
  (PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).isProjection
    (PL1.Noise.projection_isProjection 𝕜 rates)

theorem intervalProjection_norm_le (rates : ℕ → ℝ≥0) :
    ‖intervalProjection 𝕜 rates‖ ≤ PL1.projectionBound :=
  ((PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).norm_transport_le _).trans
    (PL1.Noise.norm_projection_le 𝕜 rates)

theorem intervalProjection_range_closed (rates : ℕ → ℝ≥0) :
    IsClosed ((intervalProjection 𝕜 rates).range : Set (PL1.IntervalL1 𝕜)) :=
  (intervalProjection_isProjection 𝕜 rates).isClosed_range

theorem intervalProjection_range_infiniteDimensional (rates : ℕ → ℝ≥0) :
    ¬ FiniteDimensional 𝕜 (intervalProjection 𝕜 rates).range := by
  intro h
  apply PL1.Noise.projection_range_infiniteDimensional 𝕜 rates
  exact ((PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).finiteDimensional_range_iff
    (PL1.Noise.projection 𝕜 rates)).mp h

theorem intervalProjection_range_schur_of_rates_tendsto (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun j => (rates j : ℝ)) cofinite atTop) :
    PL1.HasSchurProperty 𝕜 (intervalProjection 𝕜 rates).range :=
  ((PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).hasSchurProperty_range_iff
    (PL1.Noise.projection 𝕜 rates)).mpr
      (PL1.Noise.projection_range_hasSchurProperty_of_rates_tendsto 𝕜 rates hrates)

theorem intervalL1_not_schur : ¬ PL1.HasSchurProperty 𝕜 (PL1.IntervalL1 𝕜) := by
  intro h
  have hrange := h.submodule (intervalProjection 𝕜 PL1.Noise.constantRates).range
  have hsource := ((PL1.IntervalWalsh.walshSumContractiveRetract 𝕜).hasSchurProperty_range_iff
    (PL1.Noise.projection 𝕜 PL1.Noise.constantRates)).mp hrange
  exact PL1.Noise.constantRates_projection_range_not_schur 𝕜 hsource

theorem intervalL1_identity_not_dunfordPettis :
    ¬ PL1.IsDunfordPettis (ContinuousLinearMap.id 𝕜 (PL1.IntervalL1 𝕜)) := by
  intro h
  apply intervalL1_not_schur 𝕜
  intro x a hx
  exact h x a hx

end PL1CD
