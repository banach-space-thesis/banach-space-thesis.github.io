import PL1.MainInterpolation
import PL1.KFunctionalIntegralMeasurable

/-! # The interpolation norm as the ordinary integrable real density -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PL1.Interpolation
open Noise Walsh IntrinsicGraph

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

theorem mem_intrinsic_iff_integrable (f : Lp K 1 haar) :
    f ∈ (evalZero (dyadicSystem K rates).analysis).range ↔
      IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ) * KFunctional.value K rates t f)
        (Set.Ioi (0 : ℝ)) := by
  rw [mem_intrinsic_iff, normIntegral_eq, lt_top_iff_ne_top,
    KFunctional.continuousNorm_ne_top_iff_integrableDensity]

theorem density_nonneg_ae (f : Lp K 1 haar) :
    0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => t ^ (-3 / 2 : ℝ) * KFunctional.value K rates t f) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
  exact mul_nonneg (Real.rpow_nonneg ht0 _) (KFunctional.value_nonneg K rates ht0 f)

/-- On the finite domain, the norm is the ordinary real integral from the paper. -/
theorem normValue_eq_integral (x : (dyadicSystem K rates).IntrinsicSpace) :
    normValue K rates (evalZero (dyadicSystem K rates).analysis x) =
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-3 / 2 : ℝ) *
        KFunctional.value K rates t (evalZero (dyadicSystem K rates).analysis x) := by
  let f := evalZero (dyadicSystem K rates).analysis x
  have hi := (mem_intrinsic_iff_integrable K rates f).mp ⟨x, rfl⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (density_nonneg_ae K rates f)
  rw [normValue, normIntegral_eq]
  change (KFunctional.continuousNorm K rates f).toReal = _
  change ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ),
    t ^ (-3 / 2 : ℝ) * KFunctional.value K rates t f) = KFunctional.continuousNorm K rates f at he
  rw [← he, ENNReal.toReal_ofReal (integral_nonneg_of_ae (density_nonneg_ae K rates f))]

end PL1.Interpolation
