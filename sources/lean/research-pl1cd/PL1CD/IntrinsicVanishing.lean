import PL1CD.IntrinsicZeroVanishing
import PL1CD.CoordinateVanishing

noncomputable section
open scoped NNReal

namespace PL1CD.Variation
open PL1 PL1.Noise PL1CD.PositiveHaarOperators
variable (K : Type*) [RCLike K]

theorem intrinsic_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (T : HaarL1 K →L[K] (dyadicSystem K rates).IntrinsicSpace) :
    averagedVariation K (dyadicSystem K rates).IntrinsicSpace M N H hH T = 0 := by
  let S := dyadicSystem K rates
  have hz : averagedVariation K (PL1.L1Sum (HaarL1 K)) M N H hH
      (S.inclusion.toContinuousLinearMap.comp T) = 0 := by
    apply sum_averagedVariation_eq_zero_of_coordinates K _ M N hgrowth.monotone H hH
    intro i
    exact intrinsic_coordinate_vanishing K rates M N H hH hgrowth T i
  have h := averagedVariation_comp_ge M N H hH T S.inclusion.toContinuousLinearMap
    1 zero_le_one (fun x => by simp only [one_mul, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map]; exact le_rfl)
  rw [hz, one_mul] at h
  exact le_antisymm h (apply_nonneg _ _)

end PL1CD.Variation
