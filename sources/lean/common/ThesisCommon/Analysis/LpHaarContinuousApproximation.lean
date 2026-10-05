import ThesisCommon.Analysis.LpHaarMeanEstimates
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Dyadic averaging converges for bounded continuous functions on the interval. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical Topology BoundedContinuousFunction
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

theorem lpHaarDyadicMean_continuous_error (g : ℝ →ᵇ 𝕜) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      dist x y ≤ intervalLpDyadicRadius n → ‖g x - g y‖ ≤ ε) :
    ‖lpHaarDyadicMean 𝕜 p hp n
        (BoundedContinuousFunction.toLp p.val (volume.restrict (Icc (0 : ℝ) 1)) 𝕜 g) -
      BoundedContinuousFunction.toLp p.val (volume.restrict (Icc (0 : ℝ) 1)) 𝕜 g‖ ≤ ε := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let f : IntervalLp 𝕜 p := BoundedContinuousFunction.toLp p.val μ 𝕜 g
  have hfg : f =ᵐ[μ] g := BoundedContinuousFunction.coeFn_toLp p.val μ 𝕜 g
  have hq : ∀ᵐ x ∂μ, ∀ k : Fin (2 ^ n), x ∈ lpHaarCell n k →
      lpHaarDyadicMean 𝕜 p hp n f x = (intervalLpDyadicRadius n : 𝕜)⁻¹ *
        ∫ y in lpHaarCell n k, g y ∂μ := by
    apply ae_all_iff.mpr
    intro k
    have hi := integral_congr_ae (ae_restrict_of_ae hfg : f =ᵐ[μ.restrict (lpHaarCell n k)] g)
    dsimp [μ] at hi ⊢
    simpa only [hi] using lpHaarDyadicMean_coe 𝕜 p hp n f k
  have hbound : ∀ᵐ x ∂μ, ‖(lpHaarDyadicMean 𝕜 p hp n f - f) x‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub (lpHaarDyadicMean 𝕜 p hp n f) f, hfg, hq,
      lpHaarLevelCells_cover n] with x hsub hfx hqx hcov
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hcov
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hfx, hqx k hxk]
    have hmass : (μ.restrict (lpHaarCell n k)).real univ = intervalLpDyadicRadius n := by
      rw [measureReal_def, Measure.restrict_apply_univ, lpHaarCell_measure n k k.isLt,
        ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]
    have hnonzero : (μ.restrict (lpHaarCell n k)) univ ≠ 0 := by
      rw [Measure.restrict_apply_univ]
      exact lpHaarLevelCells_nonzero n k
    have hgi : Integrable (fun y => g y) (μ.restrict (lpHaarCell n k)) :=
      (((Lp.memLp f).integrable p.property).restrict).congr (ae_restrict_of_ae hfg)
    have hosc : ∀ᵐ y ∂(μ.restrict (lpHaarCell n k)), ‖g y - g x‖ ≤ ε := by
      filter_upwards [ae_restrict_mem (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)]
        with y hy
      exact hg y (lpHaarCell_subset n k k.isLt hy) x (lpHaarCell_subset n k k.isLt hxk)
        (lpHaarCell_dist_le n k hy hxk)
    simpa only [hmass] using lpHaarNormalizedIntegral_sub_le hnonzero hgi (g x) ε hosc
  have h := Lp.norm_le_of_ae_bound hε hbound
  simpa [μ, measureUnivNNReal] using h

theorem lpHaarDyadicRadius_tendsto : Tendsto intervalLpDyadicRadius atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem lpHaarDyadicMean_tendsto_continuous (g : ℝ →ᵇ 𝕜) :
    Tendsto (fun n => lpHaarDyadicMean 𝕜 p hp n
      (BoundedContinuousFunction.toLp p.val (volume.restrict (Icc (0 : ℝ) 1)) 𝕜 g)) atTop
      (𝓝 (BoundedContinuousFunction.toLp p.val (volume.restrict (Icc (0 : ℝ) 1)) 𝕜 g)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have huc := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).uniformContinuousOn_of_continuous
    g.continuous.continuousOn
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := (tendsto_order.mp lpHaarDyadicRadius_tendsto).2 δ hδ |>.exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine (lpHaarDyadicMean_continuous_error 𝕜 p hp g n (by linarith : 0 ≤ ε / 2) ?_).trans_lt
    (by linarith)
  intro x hx y hy hxy
  simpa only [dist_eq_norm] using (hgδ x hx y hy (hxy.trans_lt (hN n hn))).le

end ThesisCommon
