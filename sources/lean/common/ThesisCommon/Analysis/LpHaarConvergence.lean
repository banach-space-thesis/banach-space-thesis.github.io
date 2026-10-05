import ThesisCommon.Analysis.LpHaarContinuousApproximation

/-! Strong convergence of the actual contractive dyadic averages on Lp[0,1]. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace ThesisCommon

theorem lpHaarDyadicMean_dist_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (f g : IntervalLp 𝕜 p) :
    dist (lpHaarDyadicMean 𝕜 p hp n f) (lpHaarDyadicMean 𝕜 p hp n g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact ((lpHaarDyadicMean 𝕜 p hp n).le_opNorm (f - g)).trans
    ((mul_le_mul_of_nonneg_right (lpHaarDyadicMean_norm_le 𝕜 p hp n) (norm_nonneg _)).trans_eq
      (one_mul _))

/-- Dyadic averaging converges in the genuine measure-theoretic Lp norm for
every finite Banach exponent, over real or complex scalars. -/
theorem lpHaarDyadicMean_tendsto (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (f : IntervalLp 𝕜 p) :
    Tendsto (fun n => lpHaarDyadicMean 𝕜 p hp n f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hd := BoundedContinuousFunction.toLp_denseRange 𝕜 μ 𝕜 hp
  obtain ⟨g, hg⟩ := hd.exists_dist_lt f (by linarith : 0 < ε / 3)
  let v : IntervalLp 𝕜 p := BoundedContinuousFunction.toLp p.val μ 𝕜 g
  have hv : dist f v < ε / 3 := hg
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (lpHaarDyadicMean_tendsto_continuous 𝕜 p hp g)
    (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hnv : dist (lpHaarDyadicMean 𝕜 p hp n v) v < ε / 3 := hN n hn
  calc
    dist (lpHaarDyadicMean 𝕜 p hp n f) f ≤
        dist (lpHaarDyadicMean 𝕜 p hp n f) (lpHaarDyadicMean 𝕜 p hp n v) +
          dist (lpHaarDyadicMean 𝕜 p hp n v) f := dist_triangle _ _ _
    _ ≤ dist f v + (dist (lpHaarDyadicMean 𝕜 p hp n v) v + dist v f) :=
      add_le_add (lpHaarDyadicMean_dist_le 𝕜 p hp n f v) (dist_triangle _ _ _)
    _ < ε := by rw [dist_comm v f]; linarith

end ThesisCommon
