import ThesisCommon.Analysis.CompactScalarForward
import ThesisCommon.Analysis.NullSubsequence

/-! LPCK Corollary 3.2: strong forward reduction for finite-p sums. The
selected set may be required to lie in any specified infinite subset. -/
noncomputable section
open scoped ENNReal Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem lp_strong_forward_of_scalar_compact {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞)
    (hcompact : ∀ S : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p, IsCompactOperator S)
    (T : X →L[𝕜] lp (fun _ : ℕ => Y) p) {M : Set ℕ} (hM : M.Infinite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ (∀ k, e k ∈ M) ∧
      Summable (fun k => ‖(lpCoordinate p (e k)).comp T‖) ∧
      (∑' k, ‖(lpCoordinate p (e k)).comp T‖) < ε :=
  exists_increasing_summable_subsequence (fun _ => norm_nonneg _)
    (lp_coordinate_norm_tendsto_zero_of_scalar_compact hp hcompact T) hM hε

end ThesisCommon
