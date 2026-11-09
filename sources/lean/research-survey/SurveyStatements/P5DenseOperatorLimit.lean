import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Tactic.Linarith

/-! Strong limits of uniformly bounded operators from convergence on a dense
submodule. Unlike a basis construction, this also applies to vector-valued
dyadic step functions. -/

noncomputable section
set_option autoImplicit false
open Filter Set Topology

namespace SurveyStatements.P5

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem exists_operator_of_dense_limits (S : Submodule 𝕜 X)
    (hS : DenseRange S.subtypeL) (P : ℕ → X →L[𝕜] Y)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hlim : ∀ x : S, ∃ y : Y, Tendsto (fun n => P n x.val) atTop (𝓝 y)) :
    ∃ A : X →L[𝕜] Y, ‖A‖ ≤ C ∧
      ∀ x, Tendsto (fun n => P n x) atTop (𝓝 (A x)) := by
  choose v hv using hlim
  let L : S →ₗ[𝕜] Y :=
    { toFun := v
      map_add' := fun x y => by
        apply tendsto_nhds_unique (hv (x + y))
        simpa only [Submodule.coe_add, map_add] using (hv x).add (hv y)
      map_smul' := fun c x => by
        apply tendsto_nhds_unique (hv (c • x))
        simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using
          (hv x).const_smul c }
  have hL (x : S) : ‖L x‖ ≤ C * ‖x‖ := by
    exact le_of_tendsto (hv x).norm (Eventually.of_forall (fun n =>
      ((P n).le_opNorm x.val).trans
        (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg x.val))))
  let F : S →L[𝕜] Y := L.mkContinuous C hL
  have hu : IsUniformInducing S.subtypeL := isometry_subtype_coe.isUniformInducing
  let A : X →L[𝕜] Y := F.extend S.subtypeL hS hu
  have he (x : S) : A x.val = v x := ContinuousLinearMap.extend_eq _ _ _ _ x
  have hA : ‖A‖ ≤ C := by
    apply A.opNorm_le_bound hC
    intro x
    refine hS.induction_on x
      (isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro y
    change ‖A y.val‖ ≤ C * ‖y‖
    rw [he]
    exact hL y
  refine ⟨A, hA, fun x => Metric.tendsto_atTop.mpr (fun ε hε => ?_)⟩
  obtain ⟨y, hy⟩ := hS.exists_dist_lt x (div_pos hε (by linarith : 0 < 3 * (C + 1)))
  have hspan : Tendsto (fun n => P n y.val) atTop (𝓝 (A y.val)) := by
    rw [he]
    exact hv y
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hspan (ε / 3) (by linarith)
  refine ⟨M, fun n hn => ?_⟩
  have hPdist : dist (P n x) (P n y.val) ≤ C * dist x y.val := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((P n).le_opNorm (x - y.val)).trans
      (mul_le_mul_of_nonneg_right (hP n) (norm_nonneg (x - y.val)))
  have hAdist : dist (A y.val) (A x) ≤ C * dist x y.val := by
    rw [dist_comm (A y.val), dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (A.le_opNorm (x - y.val)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg (x - y.val)))
  have hsmall : C * dist x y.val < ε / 3 := by
    have hmul := mul_lt_mul_of_pos_right hy (by linarith : 0 < 3 * (C + 1))
    rw [div_mul_cancel₀ _ (by linarith : 3 * (C + 1) ≠ 0)] at hmul
    change dist x y.val * (3 * (C + 1)) < ε at hmul
    have hdist : 0 ≤ dist x y.val := dist_nonneg
    nlinarith [hdist]
  calc
    dist (P n x) (A x) ≤ dist (P n x) (P n y.val) +
        (dist (P n y.val) (A y.val) + dist (A y.val) (A x)) := by
      simpa only [add_assoc] using dist_triangle4 (P n x) (P n y.val) (A y.val) (A x)
    _ < ε := by linarith [hM n hn]

end SurveyStatements.P5
