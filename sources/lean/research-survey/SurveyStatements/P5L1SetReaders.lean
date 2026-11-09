import SurveyStatements.P5Averages
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual norm-one readers of measurable pieces of L1. Readers of
disjoint pieces have a joint l1 bound, used for mixed-norm operator tests. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace SurveyStatements.P5

theorem norm_setIntegral_le_l1_norm (s : Set ℝ)
    (f : Lp ℝ 1 unitIntervalMeasure) :
    ‖∫ x in s, f x ∂unitIntervalMeasure‖ ≤ ‖f‖ := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)).norm
  calc
    _ ≤ ∫ x in s, ‖f x‖ ∂unitIntervalMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ∂unitIntervalMeasure :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun x => norm_nonneg (f x))) hf
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

def l1SetReader (s : Set ℝ) : Lp ℝ 1 unitIntervalMeasure →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in s, f x ∂unitIntervalMeasure
      map_add' := fun f g => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact integral_add
          ((Lp.memLp f).integrable (by norm_num)).integrableOn
          ((Lp.memLp g).integrable (by norm_num)).integrableOn
      map_smul' := fun c f => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        exact integral_smul c f }
    1 (fun f => by simpa only [one_mul] using norm_setIntegral_le_l1_norm s f)

@[simp] theorem l1SetReader_apply (s : Set ℝ) (f : Lp ℝ 1 unitIntervalMeasure) :
    l1SetReader s f = ∫ x in s, f x ∂unitIntervalMeasure := rfl

theorem norm_l1SetReader_le (s : Set ℝ) : ‖l1SetReader s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem sum_norm_l1SetReader_le {ι : Type*} (F : Finset ι)
    (S : ι → Set ℝ) (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (f : Lp ℝ 1 unitIntervalMeasure) :
    ∑ i ∈ F, ‖l1SetReader (S i) f‖ ≤ ‖f‖ := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)).norm
  calc
    _ ≤ ∑ i ∈ F, ∫ x in S i, ‖f x‖ ∂unitIntervalMeasure :=
      Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)
    _ = ∫ x in ⋃ i ∈ F, S i, ‖f x‖ ∂unitIntervalMeasure :=
      (integral_biUnion_finset F hS hdisjoint (fun _ _ => hf.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ∂unitIntervalMeasure :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun x => norm_nonneg (f x))) hf
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

end SurveyStatements.P5
