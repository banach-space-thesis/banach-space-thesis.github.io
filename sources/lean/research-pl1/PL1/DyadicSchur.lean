import PL1.DyadicProjection
import PL1.DunfordPettis
import PL1.SchurApproximation

/-!
# The Schur conclusion from Dunford–Pettis resolvents

On the intrinsic graph, smoothing approximates the underlying-vector map in
operator norm. Hence Dunford–Pettis resolvents imply that map is DP. The full
countable ell1 gliding-hump argument then proves the intrinsic space Schur.
The DP property of the concrete Haar L1 resolvents remains to be discharged
by the measure-theoretic compact-restriction criterion.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1.DyadicSystem

open ResolventEstimates IntrinsicGraph

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

variable (S : DyadicSystem 𝕜 Y)

omit [CompleteSpace Y] in
theorem norm_coordinate_le (n : ℕ) (x : S.IntrinsicSpace) :
    ‖coord S.analysis n x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp) (x : L1Sum Y) n

omit [CompleteSpace Y] in
theorem norm_smoothing_error_apply_le (n : ℕ) (x : S.IntrinsicSpace) :
    ‖S.operator (n + 1) (evalZero S.analysis x) - evalZero S.analysis x‖ ≤
      dyadicRatio ^ (n + 1) * ‖x‖ := by
  have hc : (dyadicRatio ^ (n + 1))⁻¹ *
      ‖evalZero S.analysis x - S.operator (n + 1) (evalZero S.analysis x)‖ ≤ ‖x‖ := by
    have hn := S.norm_coordinate_le (n + 1) x
    rw [coord_eq] at hn
    simpa only [analysis, analysisCoordinate, smul_apply, sub_apply,
      ContinuousLinearMap.id_apply, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg _))] using hn
  have hmul := mul_le_mul_of_nonneg_left hc (pow_nonneg dyadicRatio_nonneg (n + 1))
  rw [← mul_assoc, mul_inv_cancel₀ (dyadicRatio_pow_ne_zero _), one_mul] at hmul
  simpa only [norm_sub_rev] using hmul

omit [CompleteSpace Y] in
theorem norm_smoothing_error_le (n : ℕ) :
    ‖(S.operator (n + 1)).comp (evalZero S.analysis) - evalZero S.analysis‖ ≤
      dyadicRatio ^ (n + 1) :=
  ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg dyadicRatio_nonneg _)
    (S.norm_smoothing_error_apply_le n)

set_option backward.isDefEq.respectTransparency false in
theorem smoothing_evalZero_tendsto :
    Tendsto (fun n => (S.operator (n + 1)).comp (evalZero S.analysis))
      atTop (𝓝 (evalZero S.analysis)) := by
  refine (@Metric.tendsto_atTop (S.IntrinsicSpace →L[𝕜] Y) ℕ
    inferInstance inferInstance inferInstance
    (fun n => (S.operator (n + 1)).comp (evalZero S.analysis))
    (evalZero S.analysis)).mpr ?_
  intro ε hε
  have hp : Tendsto (fun n : ℕ => dyadicRatio ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one dyadicRatio_nonneg dyadicRatio_lt_one).comp
      (tendsto_add_atTop_nat 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [show dist ((S.operator (n + 1)).comp (evalZero S.analysis)) (evalZero S.analysis) =
    ‖(S.operator (n + 1)).comp (evalZero S.analysis) - evalZero S.analysis‖ from
    @dist_eq_norm (S.IntrinsicSpace →L[𝕜] Y) inferInstance
      ((S.operator (n + 1)).comp (evalZero S.analysis)) (evalZero S.analysis)]
  exact (S.norm_smoothing_error_le n).trans_lt (hN n hn)

theorem evalZero_isDunfordPettis (hS : ∀ n, IsDunfordPettis (S.operator n)) :
    IsDunfordPettis (evalZero S.analysis) :=
  isDunfordPettis_of_tendsto (fun n => (hS (n + 1)).comp_right (evalZero S.analysis))
    S.smoothing_evalZero_tendsto

theorem hasSchurProperty_intrinsic (hS : ∀ n, IsDunfordPettis (S.operator n)) :
    HasSchurProperty 𝕜 S.IntrinsicSpace :=
  (IntrinsicGraph.hasSchurProperty_iff_evalZero_isDunfordPettis S.analysis).mpr
    (S.evalZero_isDunfordPettis hS)

theorem hasSchurProperty_projection_range (hS : ∀ n, IsDunfordPettis (S.operator n)) :
    HasSchurProperty 𝕜 S.projection.range := by
  rw [S.projection_range]
  exact S.hasSchurProperty_intrinsic hS

theorem projection_isDunfordPettis (hS : ∀ n, IsDunfordPettis (S.operator n)) :
    IsDunfordPettis S.projection :=
  isDunfordPettis_of_hasSchurProperty_range _ (S.hasSchurProperty_projection_range hS)

end PL1.DyadicSystem
