import SurveyStatements.P5PiecewiseOperatorLift
import SurveyStatements.P5Support.LpHaarDyadicMean

/-! Pointwise dyadic-grid multipliers are actual mixed-space contractions.
Their bounds are uniform in both grid depths. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def dyadicGridFunction (n : ℕ) (a : Fin (2 ^ n) → 𝕜) (x : ℝ) : 𝕜 :=
  ∑ k : Fin (2 ^ n), (P5Support.lpHaarCell n k).indicator (fun _ => a k) x

theorem dyadicGridFunction_stronglyMeasurable (n : ℕ) (a : Fin (2 ^ n) → 𝕜) :
    StronglyMeasurable (dyadicGridFunction n a) := by
  change StronglyMeasurable (fun x : ℝ => ∑ k : Fin (2 ^ n),
    (P5Support.lpHaarCell n k).indicator (fun _ => a k) x)
  exact
    (Finset.stronglyMeasurable_fun_sum (Finset.univ : Finset (Fin (2 ^ n)))
      (fun k _ => stronglyMeasurable_const.indicator
        (show MeasurableSet (P5Support.lpHaarCell n k) from measurableSet_Ioc)))

theorem norm_dyadicGridFunction_le (n : ℕ) (a : Fin (2 ^ n) → 𝕜)
    (ha : ∀ k, ‖a k‖ ≤ 1) (x : ℝ) : ‖dyadicGridFunction n a x‖ ≤ 1 := by
  let L (k : Fin (2 ^ n)) : 𝕜 →L[𝕜] 𝕜 := a k • ContinuousLinearMap.id 𝕜 𝕜
  have hL (k : Fin (2 ^ n)) : ‖L k‖ ≤ 1 := by
    change ‖a k • ContinuousLinearMap.id 𝕜 𝕜‖ ≤ 1
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
      (by simpa using ha k)
  have h := norm_disjoint_operator_indicators_le Finset.univ
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k) L
    (fun i _ j _ hij => P5Support.lpHaarLevelCells_disjoint n hij)
    (fun k _ => hL k) x (fun _ => (1 : 𝕜))
  simpa only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, mul_one, norm_one, dyadicGridFunction] using h

def mixedDyadicGridMultiply (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) (ha : ∀ i j, ‖a i j‖ ≤ 1) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  piecewiseOperatorLift Finset.univ
    (fun i : Fin (2 ^ n) => P5Support.lpHaarCell n i)
    (fun _ => measurableSet_Ioc)
    (fun i => vectorBoundedMultiply (E := 𝕜) (p := 1) (dyadicGridFunction m (a i))
      (dyadicGridFunction_stronglyMeasurable m (a i))
      (norm_dyadicGridFunction_le m (a i) (ha i)))

theorem norm_mixedDyadicGridMultiply_le (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) (ha : ∀ i j, ‖a i j‖ ≤ 1) :
    ‖mixedDyadicGridMultiply (p := p) n m a ha‖ ≤ 1 := by
  apply norm_piecewiseOperatorLift_le
  · intro i _ j _ hij
    exact P5Support.lpHaarLevelCells_disjoint n hij
  · intro i _
    exact norm_vectorBoundedMultiply_le _ _ _

end SurveyStatements.P5
