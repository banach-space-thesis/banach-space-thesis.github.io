import SurveyStatements.P5PiecewiseOperatorBounds
import SurveyStatements.P5DyadicGridMultiplication

/-! Finite dyadic-grid multiplication operators for arbitrary coefficients.
Their norm is bounded by a common coefficient bound, independently of depth. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def scalarDyadicGridOperator (n : ℕ) (a : Fin (2 ^ n) → 𝕜) :
    Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure :=
  piecewiseOperatorLift Finset.univ
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
    (fun _ => measurableSet_Ioc)
    (fun k => a k • ContinuousLinearMap.id 𝕜 𝕜)

theorem norm_scalarDyadicGridOperator_le (n : ℕ) (a : Fin (2 ^ n) → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ k, ‖a k‖ ≤ C) :
    ‖scalarDyadicGridOperator (p := p) n a‖ ≤ C := by
  apply norm_piecewiseOperatorLift_bound _ _ _ _ hC
  · intro i _ j _ hij
    exact P5Support.lpHaarLevelCells_disjoint n hij
  · intro k _
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans
      (by simpa only [mul_one] using ha k)

theorem scalarDyadicGridOperator_ae (n : ℕ) (a : Fin (2 ^ n) → 𝕜)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    scalarDyadicGridOperator n a f =ᵐ[unitIntervalMeasure]
      fun x => dyadicGridFunction n a x * f x := by
  filter_upwards [piecewiseOperatorLift_ae Finset.univ
    (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
    (fun _ => measurableSet_Ioc) (fun k => a k • ContinuousLinearMap.id 𝕜 𝕜) f]
    with x hx
  change scalarDyadicGridOperator n a f x = _
  change scalarDyadicGridOperator n a f x = _ at hx
  rw [hx]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, dyadicGridFunction, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : x ∈ P5Support.lpHaarCell n k <;> simp [hk]

def mixedDyadicGridOperator (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) :
    MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p :=
  piecewiseOperatorLift Finset.univ
    (fun i : Fin (2 ^ n) => P5Support.lpHaarCell n i)
    (fun _ => measurableSet_Ioc)
    (fun i => scalarDyadicGridOperator (p := 1) m (a i))

theorem norm_mixedDyadicGridOperator_le (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i j, ‖a i j‖ ≤ C) :
    ‖mixedDyadicGridOperator (p := p) n m a‖ ≤ C := by
  apply norm_piecewiseOperatorLift_bound _ _ _ _ hC
  · intro i _ j _ hij
    exact P5Support.lpHaarLevelCells_disjoint n hij
  · intro i _
    exact norm_scalarDyadicGridOperator_le m (a i) hC (ha i)

theorem mixedDyadicGridOperator_ae (n m : ℕ)
    (a : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) (f : MixedNorm 𝕜 p) :
    mixedDyadicGridOperator n m a f =ᵐ[unitIntervalMeasure]
      fun x => ∑ i : Fin (2 ^ n), (P5Support.lpHaarCell n i).indicator
        (fun x => scalarDyadicGridOperator (p := 1) m (a i) (f x)) x := by
  exact piecewiseOperatorLift_ae Finset.univ
    (fun i : Fin (2 ^ n) => P5Support.lpHaarCell n i)
    (fun _ => measurableSet_Ioc)
    (fun i => scalarDyadicGridOperator (p := 1) m (a i)) f

end SurveyStatements.P5
