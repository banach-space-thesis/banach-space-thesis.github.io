import SurveyStatements.P5DyadicGridRefinementValues

/-! Exact refinement identities for the actual scalar and mixed grid operators. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem scalarDyadicGridOperator_refine (n : ℕ) (a : Fin (2 ^ n) → 𝕜) :
    scalarDyadicGridOperator (p := p) (n + 1) (fun j => a (lpHaarParentIndex n j)) =
      scalarDyadicGridOperator n a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [scalarDyadicGridOperator_ae (n + 1)
    (fun j => a (lpHaarParentIndex n j)) f, scalarDyadicGridOperator_ae n a f]
    with x hf hc
  rw [hf, hc]
  change dyadicGridValue (n + 1) (fun j => a (lpHaarParentIndex n j)) x * f x =
    dyadicGridValue n a x * f x
  rw [dyadicGridValue_refine]

theorem mixedDyadicGridOperator_refine_inner (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) :
    mixedDyadicGridOperator (p := p) n (m + 1)
      (fun i j => a i (lpHaarParentIndex m j)) = mixedDyadicGridOperator n m a := by
  unfold mixedDyadicGridOperator
  simp_rw [scalarDyadicGridOperator_refine]

theorem mixedDyadicGridOperator_refine_outer (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) :
    mixedDyadicGridOperator (p := p) (n + 1) m
      (fun i j => a (lpHaarParentIndex n i) j) = mixedDyadicGridOperator n m a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [mixedDyadicGridOperator_ae (n + 1) m
    (fun i j => a (lpHaarParentIndex n i) j) f, mixedDyadicGridOperator_ae n m a f]
    with x hf hc
  rw [hf, hc]
  change dyadicGridValue (n + 1)
    (fun j => scalarDyadicGridOperator (p := 1) m (a (lpHaarParentIndex n j)) (f x)) x =
      dyadicGridValue n (fun i => scalarDyadicGridOperator (p := 1) m (a i) (f x)) x
  exact dyadicGridValue_refine (E := Lp 𝕜 1 unitIntervalMeasure) n
    (fun i => scalarDyadicGridOperator (p := 1) m (a i) (f x)) x

end SurveyStatements.P5
