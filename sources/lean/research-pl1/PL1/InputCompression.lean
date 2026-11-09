import PL1.MatrixTrace
import PL1.IntervalModel

/-! # Uniform finite-coordinate approximation of bounded interval inputs -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.InputCompression

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω] (μ : Measure Ω)

theorem norm_mask_compl_restriction_tendsto_zero
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hcover : ∀ x, ∀ᶠ n : ℕ in atTop, x ∈ A n) :
    Tendsto (fun n => ‖(L1Masks.mask μ (A n)ᶜ (hA n).compl).comp
      (OperatorDomination.restriction μ B)‖) atTop (𝓝 0) := by
  obtain ⟨G, hG, hGint, hGpos, _, hdom⟩ := OperatorDomination.exists_measurable_dominator μ B
  have ht : Tendsto (fun n => ∫ x in (A n)ᶜ, G x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ)) G
      (fun n => (hG.indicator (hA n).compl).aestronglyMeasurable) hGint
      (fun n => ae_of_all _ (fun x => by
        by_cases hx : x ∈ (A n)ᶜ
        · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hGpos x)]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact hGpos x))
      (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hcover x] with n hn
        exact (Set.indicator_of_notMem (show x ∉ (A n)ᶜ from fun h => h hn) G).symm))
    simpa only [integral_indicator (hA _).compl, integral_zero] using h
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => OperatorDomination.norm_mask_restriction_le μ B G hGint hGpos hdom _ _) ht

variable [SFinite μ]

def components (n : ℕ) : Set (ℕ × Ω) := {x | x.1 < n}

theorem measurableSet_components (n : ℕ) : MeasurableSet (components (Ω := Ω) n) :=
  measurable_fst (measurableSet_lt measurable_id measurable_const)

theorem flatten_compression (n : ℕ) (x : L1Sum (Lp 𝕜 1 μ)) :
    IntervalModel.flatten μ (MatrixTrace.compression (𝕜 := 𝕜) (Finset.range n) x) =
      L1Masks.mask (IntervalModel.disjointMeasure μ) (components n) (measurableSet_components n)
        (IntervalModel.flatten μ x) := by
  apply Lp.ext
  apply (IntervalModel.flatten_coeFn μ _).trans
  apply Filter.EventuallyEq.trans _
    (L1Masks.coeFn_mask (IntervalModel.disjointMeasure μ) (components n)
      (measurableSet_components n) (IntervalModel.flatten μ x)).symm
  have hflat := IntervalModel.flatten_coeFn μ x
  apply Filter.EventuallyEq.trans _ (hflat.indicator (s := components n)).symm
  change IntervalModel.flattenFunction μ (MatrixTrace.compression (𝕜 := 𝕜) (Finset.range n) x) =ᵐ[
    Measure.count.prod μ] (components n).indicator (IntervalModel.flattenFunction μ x)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (IntervalModel.measurable_flattenFunction μ _)
    ((IntervalModel.measurable_flattenFunction μ x).indicator (measurableSet_components n)))).mpr
  exact ae_of_all _ (fun i => by
    by_cases hi : i < n
    · exact ae_of_all _ (fun z => by
        simp only [IntervalModel.flattenFunction, MatrixTrace.compression_apply_coord,
          Finset.mem_range, hi, ite_true, components, Set.indicator_of_mem
            (show (i, z) ∈ {x : ℕ × Ω | x.1 < n} from hi)])
    · filter_upwards [Lp.coeFn_zero (E := 𝕜) (p := 1) (μ := μ)] with z hz
      simp only [IntervalModel.flattenFunction, MatrixTrace.compression_apply_coord,
        Finset.mem_range, hi, ite_false, components, Set.indicator_of_notMem
          (show (i, z) ∉ {x : ℕ × Ω | x.1 < n} from hi)]
      exact hz)

theorem norm_input_compression_error_tendsto_zero
    (B : IntervalL1 𝕜 →L[𝕜] L1Sum (Lp 𝕜 1 μ)) :
    Tendsto (fun n => ‖((ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) -
      MatrixTrace.compression (𝕜 := 𝕜) (Finset.range n)).comp B).comp
        (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)‖) atTop (𝓝 0) := by
  let e := IntervalModel.sumDisjointEquiv (𝕜 := 𝕜) μ
  have ht := norm_mask_compl_restriction_tendsto_zero (IntervalModel.disjointMeasure μ)
    ((e : L1Sum (Lp 𝕜 1 μ) →L[𝕜] Lp 𝕜 1 (IntervalModel.disjointMeasure μ)).comp B)
    components measurableSet_components (fun x => eventually_gt_atTop x.1)
  have heq (n : ℕ) : (L1Masks.mask (IntervalModel.disjointMeasure μ) (components n)ᶜ
      (measurableSet_components n).compl).comp
      (OperatorDomination.restriction (IntervalModel.disjointMeasure μ)
        ((e : L1Sum (Lp 𝕜 1 μ) →L[𝕜] Lp 𝕜 1 (IntervalModel.disjointMeasure μ)).comp B)) =
      (e : L1Sum (Lp 𝕜 1 μ) →L[𝕜] Lp 𝕜 1 (IntervalModel.disjointMeasure μ)).comp
        (((ContinuousLinearMap.id 𝕜 (L1Sum (Lp 𝕜 1 μ)) - MatrixTrace.compression (Finset.range n)).comp B).comp
          (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)) := by
    rw [← OperatorDomination.mask_compl (IntervalModel.disjointMeasure μ)
      (components n) (measurableSet_components n)]
    apply ContinuousLinearMap.ext
    intro f
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
      OperatorDomination.restriction, map_sub]
    exact congrArg (fun z => e (B (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f)) - z)
      (flatten_compression μ n (B (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f))).symm
  simpa only [heq, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp] using ht

end PL1.InputCompression
