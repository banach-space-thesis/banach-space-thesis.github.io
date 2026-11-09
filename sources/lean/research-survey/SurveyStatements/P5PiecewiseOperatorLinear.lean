import SurveyStatements.P5PiecewiseOperatorLift

/-! Linearity of actual finite piecewise families in their operator values. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem piecewiseOperatorLift_add {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (L M : ι → E →L[𝕜] E) :
    piecewiseOperatorLift (p := p) F S hS (fun i => L i + M i) =
      piecewiseOperatorLift F S hS L + piecewiseOperatorLift F S hS M := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [piecewiseOperatorLift_ae F S hS (fun i => L i + M i) f,
    piecewiseOperatorLift_ae F S hS L f, piecewiseOperatorLift_ae F S hS M f,
    Lp.coeFn_add (piecewiseOperatorLift F S hS L f)
      (piecewiseOperatorLift F S hS M f)] with x hLM hL hM hadd
  simp only [Pi.add_apply] at hadd
  change (piecewiseOperatorLift F S hS (fun i => L i + M i) f) x =
    (piecewiseOperatorLift F S hS L f + piecewiseOperatorLift F S hS M f) x
  rw [hLM, hadd, hL, hM, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ S i <;> simp [hi, ContinuousLinearMap.add_apply]

theorem piecewiseOperatorLift_smul {ι : Type*} (F : Finset ι) (S : ι → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (L : ι → E →L[𝕜] E) (c : 𝕜) :
    piecewiseOperatorLift (p := p) F S hS (fun i => c • L i) =
      c • piecewiseOperatorLift F S hS L := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [piecewiseOperatorLift_ae F S hS (fun i => c • L i) f,
    piecewiseOperatorLift_ae F S hS L f,
    Lp.coeFn_smul c (piecewiseOperatorLift F S hS L f)] with x hc hL hsmul
  simp only [Pi.smul_apply] at hsmul
  change (piecewiseOperatorLift F S hS (fun i => c • L i) f) x =
    (c • piecewiseOperatorLift F S hS L f) x
  rw [hc, hsmul, hL, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ S i <;> simp [hi, ContinuousLinearMap.smul_apply]

end SurveyStatements.P5
