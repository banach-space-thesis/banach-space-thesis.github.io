import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Sequences

/-! Simultaneous limits of countably many bounded scalar traces. This is
the compactness step used to stabilise Haar multipliers. -/

noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜] [Countable I]

theorem haar_countable_trace_cluster (v : ℕ → I → 𝕜) {M : ℝ}
    (hv : ∀ n i, ‖v n i‖ ≤ M) :
    ∃ a : I → 𝕜, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ i, ‖a i‖ ≤ M) ∧ ∀ i, Tendsto (fun n => v (r n) i) atTop (𝓝 (a i)) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let K := Metric.closedBall (0 : 𝕜) M
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  let w : ℕ → I → K := fun n i => ⟨v n i, by simpa [K, Metric.mem_closedBall, dist_zero_right] using hv n i⟩
  obtain ⟨a, r, hr, ha⟩ := CompactSpace.tendsto_subseq w
  refine ⟨fun i => (a i).val, r, hr, fun i => ?_, fun i => ?_⟩
  · simpa only [dist_zero_right] using (Metric.mem_closedBall.mp (a i).property)
  · exact ((continuous_subtype_val.comp (continuous_apply i)).tendsto a).comp ha

end ThesisCommon
