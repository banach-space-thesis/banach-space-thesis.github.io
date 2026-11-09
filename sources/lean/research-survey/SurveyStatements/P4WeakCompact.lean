import SurveyStatements.P4Definitions
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weak compactness with the actual weak topology

Basic facts used by the paper's approximation and interpolation construction.
The compact-cover formulation is proved equivalent to the closure definition.
-/

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Pointwise

namespace SurveyStatements.P4

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The canonical map from the weak topology into the weak-star bidual. -/
def weakBidualInclusion : WeakSpace 𝕜 F →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 F) where
  toLinearMap := (StrongDual.toWeakDual.toLinearMap.comp
    (NormedSpace.inclusionInDoubleDual 𝕜 F).toLinearMap).comp (toWeakSpace 𝕜 F).symm.toLinearMap
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact WeakBilin.eval_continuous _ f

/-- Hahn-Banach makes the weak topology Hausdorff: its canonical bidual map
is a topological embedding. -/
theorem isEmbedding_weakBidualInclusion :
    Topology.IsEmbedding (weakBidualInclusion (𝕜 := 𝕜) (F := F)) := by
  constructor
  · constructor
    change TopologicalSpace.induced
      (fun x : WeakSpace 𝕜 F => fun f : StrongDual 𝕜 F => f x)
      Pi.topologicalSpace = TopologicalSpace.induced weakBidualInclusion
        (TopologicalSpace.induced
          (fun ξ : WeakDual 𝕜 (StrongDual 𝕜 F) => fun f : StrongDual 𝕜 F => ξ f)
          Pi.topologicalSpace)
    rw [induced_compose]
    rfl
  · intro x y hxy
    apply (toWeakSpace 𝕜 F).symm.injective
    apply (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := F)).injective
    exact StrongDual.toWeakDual.injective hxy

/-- Weak relative compactness of the unit-ball image is equivalent to its
being contained in a weakly compact set. -/
theorem weaklyCompact_iff_compact_cover (T : E →L[𝕜] F) :
    IsWeaklyCompactOperator 𝕜 T ↔
      ∃ K : Set (WeakSpace 𝕜 F), IsCompact K ∧
        ∀ x : E, ‖x‖ ≤ 1 → toWeakSpace 𝕜 F (T x) ∈ K := by
  letI : T2Space (WeakSpace 𝕜 F) :=
    (isEmbedding_weakBidualInclusion (𝕜 := 𝕜) (F := F)).t2Space
  constructor
  · intro h
    refine ⟨closure ((toWeakSpace 𝕜 F) '' (T '' Metric.closedBall (0 : E) 1)), h, ?_⟩
    intro x hx
    apply subset_closure
    exact ⟨T x, ⟨x, by simpa using hx, rfl⟩, rfl⟩
  · rintro ⟨K, hK, hTK⟩
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hTK x (by simpa using hx)

theorem weaklyCompact_zero : IsWeaklyCompactOperator 𝕜 (0 : E →L[𝕜] F) := by
  apply (weaklyCompact_iff_compact_cover _).mpr
  exact ⟨{0}, isCompact_singleton, by intro x hx; simp⟩

theorem IsWeaklyCompactOperator.comp_left {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator 𝕜 T) (S : F →L[𝕜] G) :
    IsWeaklyCompactOperator 𝕜 (S.comp T) := by
  obtain ⟨K, hK, hTK⟩ := (weaklyCompact_iff_compact_cover T).mp hT
  apply (weaklyCompact_iff_compact_cover _).mpr
  refine ⟨WeakSpace.map S '' K, hK.image (WeakSpace.map S).continuous, ?_⟩
  intro x hx
  exact ⟨toWeakSpace 𝕜 F (T x), hTK x hx, rfl⟩

theorem IsWeaklyCompactOperator.comp_right {T : E →L[𝕜] F}
    (hT : IsWeaklyCompactOperator 𝕜 T) (S : G →L[𝕜] E) :
    IsWeaklyCompactOperator 𝕜 (T.comp S) := by
  obtain ⟨K, hK, hTK⟩ := (weaklyCompact_iff_compact_cover T).mp hT
  let r : ℝ := ‖S‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a : 𝕜 := r
  have ha : a ≠ 0 := by simpa [a] using ne_of_gt hr
  have hna : ‖a‖ = r := by simp [a, abs_of_pos hr]
  apply (weaklyCompact_iff_compact_cover _).mpr
  refine ⟨(fun y : WeakSpace 𝕜 F => a • y) '' K,
    hK.image (continuous_const.smul continuous_id), ?_⟩
  intro x hx
  have hSx : ‖S x‖ ≤ r := (S.le_opNorm x).trans <|
    (mul_le_of_le_one_right (norm_nonneg S) hx).trans (by dsimp [r]; linarith)
  have hunit : ‖a⁻¹ • S x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, ← div_eq_inv_mul]
    exact (div_le_one hr).mpr hSx
  refine ⟨toWeakSpace 𝕜 F (T (a⁻¹ • S x)), hTK _ hunit, ?_⟩
  change toWeakSpace 𝕜 F (a • T (a⁻¹ • S x)) = _
  simp [map_smul, smul_smul, ha]

end SurveyStatements.P4
