import ThesisCommon.Analysis.WeakDualEvaluation
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Goldstine's theorem, proved by separation in the actual weak-star
topology. Continuous weak-star functionals are evaluations by the preceding
module; no bidual density assertion is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def weakStarBidualInclusion : E →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 E) :=
  NormedSpace.Dual.continuousLinearMapToWeakDual.comp (NormedSpace.inclusionInDoubleDual 𝕜 E)

theorem weakStarBidualInclusion_apply (x : E) (f : StrongDual 𝕜 E) :
    weakStarBidualInclusion x f = f x := rfl

theorem dual_norm_le_of_re_unitBall_bound (f : StrongDual 𝕜 E) {C : ℝ}
    (h : ∀ x : E, ‖x‖ ≤ 1 → RCLike.re (f x) ≤ C) : ‖f‖ ≤ C := by
  have hC : 0 ≤ C := by simpa using h 0 (by simp)
  have hb : ∀ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ ≤ C := by
    intro x hx
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    by_cases hf : f x = 0
    · simpa [hf] using hC
    let a : 𝕜 := (‖f x‖ : 𝕜) / f x
    have ha : ‖a‖ = 1 := by simp [a, norm_div, hf]
    have hax : ‖a • x‖ ≤ 1 := by simpa only [norm_smul, ha, one_mul] using hx'
    have hfa : f (a • x) = (‖f x‖ : 𝕜) := by
      simp only [map_smul, smul_eq_mul, a, div_mul_cancel₀ _ hf]
    simpa only [hfa, RCLike.ofReal_re] using h (a • x) hax
  simpa only [div_one] using ContinuousLinearMap.opNorm_bound_of_ball_bound zero_lt_one C f hb

theorem goldstine_unitBall (ξ : StrongDual 𝕜 (StrongDual 𝕜 E)) (hξ : ‖ξ‖ ≤ 1) :
    StrongDual.toWeakDual ξ ∈ closure
      ((weakStarBidualInclusion (𝕜 := 𝕜) (E := E)) '' Metric.closedBall 0 1) := by
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars _ 𝕜 _
  letI : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
  let L : WeakDual 𝕜 (StrongDual 𝕜 E) →ₗ[ℝ] (StrongDual 𝕜 E → 𝕜) :=
    { toFun := fun η f => η f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : LocallyConvexSpace ℝ (WeakDual 𝕜 (StrongDual 𝕜 E)) :=
    LocallyConvexSpace.induced L
  let J := weakStarBidualInclusion (𝕜 := 𝕜) (E := E)
  have hconv : Convex ℝ (J '' Metric.closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) (1 : ℝ)).linear_image (J.restrictScalars ℝ).toLinearMap
  by_contra hnot
  obtain ⟨ψ, c, hc, hψ⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := 𝕜) hconv.closure isClosed_closure hnot
  obtain ⟨f, hf⟩ := weakDual_functional_eq_eval ψ
  have hnorm : ‖f‖ ≤ c := dual_norm_le_of_re_unitBall_bound f fun x hx => by
    have hJx : J x ∈ closure (J '' Metric.closedBall 0 1) :=
      subset_closure ⟨x, by simpa using hx, rfl⟩
    simpa only [hf, weakStarBidualInclusion_apply, J] using (hc (J x) hJx).le
  have hle : RCLike.re (ψ (StrongDual.toWeakDual ξ)) ≤ c := by
    rw [hf]
    exact (RCLike.re_le_norm _).trans ((ξ.le_opNorm f).trans
      ((mul_le_mul_of_nonneg_right hξ (norm_nonneg f)).trans (by simpa using hnorm)))
  exact (not_lt_of_ge hle) hψ

end ThesisCommon
