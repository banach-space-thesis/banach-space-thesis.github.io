import SurveyStatements.P5DyadicGridOperator
import SurveyStatements.P5Support.LpHaarRootMean

/-! The actual scalar and mixed root grids are scalar identities. The
proof uses the AE coverage of the unit interval by its root dyadic cell. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem scalarDyadicGridOperator_zero (a : Fin (2 ^ 0) → 𝕜) :
    scalarDyadicGridOperator (p := p) 0 a =
      a 0 • ContinuousLinearMap.id 𝕜 (Lp 𝕜 p unitIntervalMeasure) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [scalarDyadicGridOperator_ae 0 a f, lpHaarRootCell_ae,
    Lp.coeFn_smul (a 0) f] with x hgrid hroot hsmul
  change scalarDyadicGridOperator 0 a f x = ((a 0) • f) x
  rw [hgrid, hsmul]
  change (∑ k : Fin 1, (lpHaarCell 0 k.val).indicator (fun _ => a k) x) * f x =
    a 0 • f x
  rw [Fin.sum_univ_one]
  change (lpHaarCell 0 0).indicator (fun _ => a 0) x * f x = a 0 • f x
  rw [Set.indicator_of_mem hroot]
  simp only [smul_eq_mul]

theorem mixedDyadicGridOperator_zero (a : Fin (2 ^ 0) → Fin (2 ^ 0) → 𝕜) :
    mixedDyadicGridOperator (p := p) 0 0 a =
      a 0 0 • ContinuousLinearMap.id 𝕜 (MixedNorm 𝕜 p) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [mixedDyadicGridOperator_ae 0 0 a f, lpHaarRootCell_ae,
    Lp.coeFn_smul (a 0 0) f] with x hgrid hroot hsmul
  change mixedDyadicGridOperator 0 0 a f x = ((a 0 0) • f) x
  rw [hgrid, hsmul]
  change (∑ i : Fin 1, (lpHaarCell 0 i.val).indicator
    (fun x => scalarDyadicGridOperator (p := 1) 0 (a i) (f x)) x) = a 0 0 • f x
  rw [Fin.sum_univ_one]
  change (lpHaarCell 0 0).indicator
    (fun x => scalarDyadicGridOperator (p := 1) 0 (a 0) (f x)) x = a 0 0 • f x
  rw [Set.indicator_of_mem hroot]
  rw [scalarDyadicGridOperator_zero]
  rfl

end SurveyStatements.P5
