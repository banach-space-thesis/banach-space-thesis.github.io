import PL1CD.IntrinsicVanishing
import PL1CD.ProjectionFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped NNReal

namespace PL1CD.Variation
open PL1 PL1.Noise PL1CD.PositiveHaarOperators
variable (K : Type) [RCLike K]

theorem projection_range_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (T : HaarL1 K →L[K] (PL1.Noise.projection K rates).range) :
    averagedVariation K (PL1.Noise.projection K rates).range M N H hH T = 0 := by
  change HaarL1 K →L[K] (dyadicSystem K rates).projection.range at T
  change averagedVariation K (dyadicSystem K rates).projection.range M N H hH T = 0
  revert T
  rw [DyadicSystem.projection_range]
  intro T
  exact intrinsic_vanishing K rates M N H hH hgrowth T

theorem interval_range_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (T : HaarL1 K →L[K] (PL1CD.intervalProjection K rates).range) :
    averagedVariation K (PL1CD.intervalProjection K rates).range M N H hH T = 0 := by
  let R := IntervalWalsh.walshSumContractiveRetract K
  let P := PL1.Noise.projection K rates
  let e := R.rangeEquiv P
  let W := e.symm.toContinuousLinearMap
  have hnorm (x : (R.transport P).range) : ‖W x‖ = ‖x‖ := by
    change ‖e.symm x‖ = ‖x‖
    have h := R.rangeEquiv_norm P (e.symm x)
    change ‖e (e.symm x)‖ = ‖e.symm x‖ at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hz := projection_range_vanishing K rates M N H hH hgrowth (W.comp T)
  have h := averagedVariation_comp_ge M N H hH T W 1 zero_le_one
    (fun x => by rw [one_mul]; exact le_of_eq (hnorm x).symm)
  rw [hz, one_mul] at h
  exact le_antisymm h (apply_nonneg _ _)

end PL1CD.Variation
