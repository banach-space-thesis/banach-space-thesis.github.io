import SurveyStatements.P4TailConvexRieszReal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.Algebra.Module.WeakDual

/-! Uniformly bounded, pointwise null continuous scalar functions on a
compact Hausdorff space are weakly null. The proof uses actual finite Riesz
measures and dominated convergence. -/

noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory

namespace SurveyStatements.P4

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Every bounded real functional tends to zero on a uniformly bounded,
pointwise null sequence of real continuous functions on a compact space. -/
theorem continuousMap_uniformlyBounded_pointwiseNull_apply
    (f : ℕ → C(K, ℝ)) (C : ℝ) (hbound : ∀ n, ‖f n‖ ≤ C)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 0))
    (μ : C(K, ℝ) →L[ℝ] ℝ) : Tendsto (fun n => μ (f n)) atTop (𝓝 0) := by
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  have hint (ν : Measure K) [IsFiniteMeasure ν] :
      Tendsto (fun n => ∫ t, f n t ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := ν) (f := fun _ => (0 : ℝ))
      (fun _ => C) (fun n => (f n).continuous.aestronglyMeasurable)
      (integrable_const C) (fun n => Filter.Eventually.of_forall fun t =>
        ((f n).norm_coe_le_norm t).trans (hbound n))
      (Filter.Eventually.of_forall hpoint)
    simpa using h
  have h := (hint (continuousMapRieszPositive μ)).sub (hint (continuousMapRieszNegative μ))
  simpa only [sub_zero, ← continuousMap_real_riesz_representation] using h

/-- The same convergence in the actual weak topology of C(K,ℝ). -/
theorem continuousMap_uniformlyBounded_pointwiseNull_weak
    (f : ℕ → C(K, ℝ)) (C : ℝ) (hbound : ∀ n, ‖f n‖ ≤ C)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 0)) :
    Tendsto (fun n => toWeakSpace ℝ C(K, ℝ) (f n)) atTop (𝓝 0) := by
  have hinj : Function.Injective (topDualPairing ℝ C(K, ℝ)).flip := by
    intro f g hfg
    apply (NormedSpace.inclusionInDoubleDualLi ℝ (E := C(K, ℝ))).injective
    apply ContinuousLinearMap.ext
    intro μ
    exact LinearMap.congr_fun hfg μ
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro μ
  simpa only [map_zero] using
    continuousMap_uniformlyBounded_pointwiseNull_apply f C hbound hpoint μ

end SurveyStatements.P4
