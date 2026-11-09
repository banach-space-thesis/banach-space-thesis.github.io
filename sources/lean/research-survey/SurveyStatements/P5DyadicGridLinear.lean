import SurveyStatements.P5DyadicGridOperator
import SurveyStatements.P5PiecewiseOperatorLinear

/-! Exact coefficient linearity of actual dyadic-grid multipliers. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def scalarDyadicGridLinear (n : ℕ) : (Fin (2 ^ n) → 𝕜) →ₗ[𝕜]
    (Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure) where
  toFun := scalarDyadicGridOperator n
  map_add' := by
    intro a b
    have hvalues : (fun k => (a k + b k) • ContinuousLinearMap.id 𝕜 𝕜) =
        (fun k => a k • ContinuousLinearMap.id 𝕜 𝕜 +
          b k • ContinuousLinearMap.id 𝕜 𝕜) := by
      funext k
      exact add_smul (a k) (b k) (ContinuousLinearMap.id 𝕜 𝕜)
    change piecewiseOperatorLift (p := p) Finset.univ
      (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
      (fun _ => measurableSet_Ioc)
      (fun k => (a k + b k) • ContinuousLinearMap.id 𝕜 𝕜) = _
    rw [hvalues]
    exact piecewiseOperatorLift_add (p := p) Finset.univ
        (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
        (fun _ => measurableSet_Ioc)
        (fun k => a k • ContinuousLinearMap.id 𝕜 𝕜)
        (fun k => b k • ContinuousLinearMap.id 𝕜 𝕜)
  map_smul' := by
    intro c a
    simpa only [scalarDyadicGridOperator, Pi.smul_apply, RingHom.id_apply, smul_smul] using
      piecewiseOperatorLift_smul (p := p) Finset.univ
        (fun k : Fin (2 ^ n) => P5Support.lpHaarCell n k)
        (fun _ => measurableSet_Ioc)
        (fun k => a k • ContinuousLinearMap.id 𝕜 𝕜) c

def mixedDyadicGridLinear (n m : ℕ) :
    (Fin (2 ^ n) → Fin (2 ^ m) → 𝕜) →ₗ[𝕜]
      (MixedNorm 𝕜 p →L[𝕜] MixedNorm 𝕜 p) where
  toFun := mixedDyadicGridOperator n m
  map_add' := by
    intro a b
    have hscalar (i : Fin (2 ^ n)) :
        scalarDyadicGridOperator (p := 1) m ((a + b) i) =
          scalarDyadicGridOperator m (a i) + scalarDyadicGridOperator m (b i) :=
      map_add (scalarDyadicGridLinear (𝕜 := 𝕜) (p := 1) m) (a i) (b i)
    unfold mixedDyadicGridOperator
    simp_rw [hscalar]
    exact piecewiseOperatorLift_add _ _ _ _ _
  map_smul' := by
    intro c a
    have hscalar (i : Fin (2 ^ n)) :
        scalarDyadicGridOperator (p := 1) m ((c • a) i) =
          c • scalarDyadicGridOperator m (a i) :=
      map_smul (scalarDyadicGridLinear (𝕜 := 𝕜) (p := 1) m) c (a i)
    simp only [RingHom.id_apply]
    unfold mixedDyadicGridOperator
    simp_rw [hscalar]
    exact piecewiseOperatorLift_smul _ _ _ _ _

theorem norm_mixedDyadicGridOperator_sub_le (n m : ℕ)
    (a b : Fin (2 ^ n) → Fin (2 ^ m) → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i j, ‖a i j - b i j‖ ≤ C) :
    ‖mixedDyadicGridOperator (p := p) n m a - mixedDyadicGridOperator n m b‖ ≤ C := by
  change ‖(mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) n m) a -
    (mixedDyadicGridLinear (𝕜 := 𝕜) (p := p) n m) b‖ ≤ C
  rw [← map_sub]
  exact norm_mixedDyadicGridOperator_le n m (a - b) hC hab

end SurveyStatements.P5
