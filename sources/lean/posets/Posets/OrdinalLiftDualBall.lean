import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.DenseEmbedding

/-! The weak-star dual ball of a separable normed space is compact and
metrizable, via evaluation on an actual countable dense sequence. -/
noncomputable section
open Set Topology TopologicalSpace
namespace Posets
variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

abbrev ordinalLiftDualBall (r : ℝ) :=
  {φ : WeakDual 𝕜 E // ‖WeakDual.toStrongDual φ‖ ≤ r}

instance ordinalLiftDualBall_compactSpace (r : ℝ) : CompactSpace (ordinalLiftDualBall 𝕜 E r) := by
  apply isCompact_iff_compactSpace.mp
  simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right] using
    WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 E) r

theorem ordinalLiftDualBall_metrizable [SeparableSpace E] (r : ℝ) :
    MetrizableSpace (ordinalLiftDualBall 𝕜 E r) := by
  let e : ordinalLiftDualBall 𝕜 E r → (ℕ → 𝕜) := fun φ n => φ.val (denseSeq E n)
  have he : Continuous e := continuous_pi fun n =>
    (WeakDual.eval_continuous (denseSeq E n)).comp continuous_subtype_val
  have hi : Function.Injective e := by
    intro φ ψ heq
    apply Subtype.ext
    apply DFunLike.ext
    have h := (denseRange_denseSeq E).equalizer
      (WeakDual.toStrongDual φ.val).continuous (WeakDual.toStrongDual ψ.val).continuous heq
    intro x
    exact congrFun h x
  exact (he.isClosedEmbedding hi).isEmbedding.metrizableSpace

end Posets
