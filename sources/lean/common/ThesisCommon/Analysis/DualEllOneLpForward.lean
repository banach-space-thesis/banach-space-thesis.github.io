import ThesisCommon.Analysis.LpCoordinateDualGrowth
import ThesisCommon.Analysis.CompactScalarForward

/-! Finite-p forward coordinate decay for coefficients with an actual
ell-one dual. Scalar weak nullity and Schur give norm decay; norming
postcompositions then give the vector-valued statement. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem scalar_lp_coordinate_norm_tendsto_zero_of_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p) :
    Tendsto (fun n => ‖(lpCoordinate p n).comp T‖) atTop (𝓝 0) := by
  have ht := scalar_schur_of_equiv_ellOne d
    (fun n => (lpCoordinate p n).comp T)
    (fun φ => (lp_coordinate_comp_weak_null p hp T φ).mono_left atTop_le_cofinite)
  simpa only [norm_zero] using ht.norm

theorem lp_coordinate_norm_tendsto_zero_of_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : ℕ => Y) p) :
    Tendsto (fun n => ‖(lpCoordinate p n).comp T‖) atTop (𝓝 0) := by
  choose f hf hnorm using fun n => exists_norming_postcomposition ((lpCoordinate p n).comp T)
  let D := lpDiagonal p f 1 zero_le_one hf
  let S := D.comp T
  have hS := scalar_lp_coordinate_norm_tendsto_zero_of_dual_equiv_ellOne d hp S
  have heq : ∀ n, (lpCoordinate p n).comp S = (f n).comp ((lpCoordinate p n).comp T) := by
    intro n
    ext x
    rfl
  have hbound : ∀ n, ‖(lpCoordinate p n).comp T‖ ≤ 2 * ‖(lpCoordinate p n).comp S‖ := by
    intro n
    rw [heq]
    exact hnorm n
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using hS.const_mul 2)

end ThesisCommon
