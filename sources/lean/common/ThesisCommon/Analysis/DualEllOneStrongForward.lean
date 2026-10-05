import ThesisCommon.Analysis.DualEllOneLpForward
import ThesisCommon.Analysis.NullSubsequence

/-! The finite-p forward selection and upper-triangular construction from the proved Schur argument on an actual ell-one dual. -/
noncomputable section
open scoped ENNReal Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y I : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem lp_strong_forward_of_dual_equiv_ellOne {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞)
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (T : X →L[𝕜] lp (fun _ : ℕ => Y) p) {M : Set ℕ} (hM : M.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ (∀ k, e k ∈ M) ∧
      Summable (fun k => ‖(lpCoordinate p (e k)).comp T‖) ∧
      (∑' k, ‖(lpCoordinate p (e k)).comp T‖) < ε :=
  exists_increasing_summable_subsequence (fun _ => norm_nonneg _)
    (lp_coordinate_norm_tendsto_zero_of_dual_equiv_ellOne d hp T) hM hε

end ThesisCommon

