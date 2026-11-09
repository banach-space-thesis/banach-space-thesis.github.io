import PL1.NoiseTraceObstruction
import PL1.NoiseHypercontractivity
import PL1.PartialMainTheorems

/-!
# Unconditional trace and factorization obstructions for the actual example

The sharp hypercontractivity theorem supplies every smoothing premise.
Consequently these conclusions about the actual constant-rate projection
have no unproved operator-theoretic hypotheses. Excluding all L1 subspaces
still requires the separate subspace-to-complemented-subspace argument.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace PL1.Noise
open Walsh NoiseHypercontractivity

def traceCutoff (m : ℕ) : ℝ≥0 := ⟨(dyadicTime m : ℝ), (dyadicTime m).property.le⟩

theorem traceCutoff_pos (m : ℕ) : 0 < traceCutoff m := (dyadicTime m).property

theorem tendsto_traceCutoff :
    Tendsto (fun m => (traceCutoff m : ℝ)) atTop (𝓝 0) := tendsto_dyadicTime

variable (𝕜 : Type*) [RCLike 𝕜]

theorem constant_resolvent_hasVanishingDyadicTrace (t : PositiveTime) :
    HasVanishingDyadicTrace (resolventL1 𝕜 constantRates t) := by
  apply resolvent_hasVanishingDyadicTrace_of_noise_smoothing 𝕜 constantRates t
    traceCutoff tendsto_traceCutoff (fun m => exponent (traceCutoff m))
    (fun m => exponent_lt_two _ (traceCutoff_pos m))
    (fun m => positiveTimeNoiseL2 𝕜 (traceCutoff m))
  intro m g f hgf
  rw [positiveTimeNoiseL2_overlap]
  congr 1
  apply Lp.ext
  exact hgf.trans (ProbabilityLp.coeFn_inclusion haar 1 (exponent (traceCutoff m))
    (exponent_ge_one _) f).symm

theorem constant_projection_hasVanishingDyadicTrace :
    HasVanishingDyadicTrace (projection 𝕜 constantRates) :=
  projection_hasVanishingDyadicTrace_of_resolvents 𝕜 constantRates
    (constant_resolvent_hasVanishingDyadicTrace 𝕜)

theorem constant_projection_identity_distance
    (A : L1Sum (Lp 𝕜 1 haar) →L[𝕜] IntervalL1 𝕜)
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 haar)) :
    1 ≤ ‖DyadicTrace.restrictLinfty (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) -
      A.comp ((projection 𝕜 constantRates).comp B))‖ :=
  (constant_projection_hasVanishingDyadicTrace 𝕜).one_le_norm_id_sub A B

theorem constant_projection_not_factors_identity
    (A : L1Sum (Lp 𝕜 1 haar) →L[𝕜] IntervalL1 𝕜)
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 haar)) :
    A.comp ((projection 𝕜 constantRates).comp B) ≠
      ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) :=
  (constant_projection_hasVanishingDyadicTrace 𝕜).not_factors_identity A B

theorem constant_intervalProjection_hasVanishingDyadicTrace :
    HasVanishingDyadicTrace (intervalProjection 𝕜 constantRates) :=
  ((constant_projection_hasVanishingDyadicTrace 𝕜).comp_right
    (IntervalWalsh.walshSumContractiveRetract 𝕜).retraction).comp_left
      (IntervalWalsh.walshSumContractiveRetract 𝕜).embedding.toContinuousLinearMap

theorem constant_intervalProjection_identity_distance
    (A B : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    1 ≤ ‖DyadicTrace.restrictLinfty (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) -
      A.comp ((intervalProjection 𝕜 constantRates).comp B))‖ :=
  (constant_intervalProjection_hasVanishingDyadicTrace 𝕜).one_le_norm_id_sub A B

theorem constant_intervalProjection_not_factors_identity
    (A B : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) :
    A.comp ((intervalProjection 𝕜 constantRates).comp B) ≠
      ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) :=
  (constant_intervalProjection_hasVanishingDyadicTrace 𝕜).not_factors_identity A B

end PL1.Noise
