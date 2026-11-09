import PL1.KFunctionalIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the continuous interpolation density on positive time. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PL1.DyadicInterpolation

theorem integrand_aemeasurable {k : ℝ → ℝ} (hmono : MonotoneOn k (Ici (0 : ℝ))) :
    AEMeasurable (integrand k) (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Monotone (fun t : ℝ => k (max t 0)) := by
    intro s t hst
    exact hmono (Set.mem_Ici.mpr (le_max_right s 0))
      (Set.mem_Ici.mpr (le_max_right t 0)) (max_le_max_right 0 hst)
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * k (max t 0))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const _).mul hm.measurable)
  apply hf.aemeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [integrand, max_eq_left (Set.mem_Ioi.mp ht).le]

end PL1.DyadicInterpolation

namespace PL1.KFunctional
open Noise Walsh

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

theorem interpolationDensity_aemeasurable (f : Lp K 1 haar) :
    AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f))
      (volume.restrict (Ioi (0 : ℝ))) :=
  DyadicInterpolation.integrand_aemeasurable (monotoneOn_value K rates f)

theorem continuousNorm_ne_top_iff_integrableDensity (f : Lp K 1 haar) :
    continuousNorm K rates f ≠ ⊤ ↔
      IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ) * value K rates t f) (Ioi (0 : ℝ)) := by
  have h := integrable_toReal_iff (interpolationDensity_aemeasurable K rates f)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))
  have heq : (fun t : ℝ => (ENNReal.ofReal (t ^ (-3 / 2 : ℝ) * value K rates t f)).toReal)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => t ^ (-3 / 2 : ℝ) * value K rates t f) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (Set.mem_Ioi.mp ht).le
    exact ENNReal.toReal_ofReal
      (mul_nonneg (Real.rpow_nonneg ht0 _) (value_nonneg K rates ht0 f))
  exact h.symm.trans (integrable_congr heq)

end PL1.KFunctional
