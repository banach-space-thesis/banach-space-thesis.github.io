import ThesisCommon.Analysis.IntegralKernelTests
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Continuous real linear maps on a finite-measure L1 space are determined
by their values on measurable indicators. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem indicatorConstLp_eq_smul_lOneIndicator (s : Set X) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : ℝ) :
    indicatorConstLp 1 hs hμs c = c • lOneIndicator μ s hs := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (lOneIndicator μ s hs), lOneIndicator_coe (μ := μ) s hs] with x hx hx' hx''
  rw [hx, hx', Pi.smul_apply, hx'']
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem lOne_continuousLinearMap_ext_indicators (S T : Lp ℝ 1 μ →L[ℝ] F)
    (h : ∀ (s : Set X) (hs : MeasurableSet s), S (lOneIndicator μ s hs) = T (lOneIndicator μ s hs)) :
    S = T := by
  apply ContinuousLinearMap.ext
  apply Lp.induction (p := 1) (by norm_num) (fun f => S f = T f)
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_lOneIndicator,
      map_smul, map_smul, h s hs]
  · intro f g hf hg _ hSf hSg
    simp only [map_add, hSf, hSg]
  · exact isClosed_eq S.continuous T.continuous

end ThesisCommon
