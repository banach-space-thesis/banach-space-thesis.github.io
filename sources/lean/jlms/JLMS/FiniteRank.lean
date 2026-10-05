import JLMS.EssentialNorm
import Mathlib.Analysis.RCLike.Lemmas

/-!
# Finite-rank maps are compact

This bridges mathlib's finite-dimensional and compact-operator APIs for the
finite-rank perturbations used in Sections 4, 5 and 7 of the paper.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bounded map with finite-dimensional range is compact over ℝ or ℂ. -/
theorem isCompactOperator_of_finiteRank (T : E →L[𝕜] F)
    (hT : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) : IsCompactOperator T := by
  let W := LinearMap.range T.toLinearMap
  letI : FiniteDimensional 𝕜 W := hT
  letI : ProperSpace W := FiniteDimensional.proper_rclike 𝕜 W
  refine ⟨Subtype.val '' Metric.closedBall (0 : W) ‖T‖,
    (isCompact_closedBall (0 : W) ‖T‖).image continuous_subtype_val, ?_⟩
  apply Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) zero_lt_one)
  intro x hx
  refine ⟨⟨T x, ⟨x, rfl⟩⟩, ?_, rfl⟩
  apply mem_closedBall_zero_iff.mpr
  change ‖T x‖ ≤ ‖T‖
  have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  exact (T.le_opNorm x).trans (by
    simpa using mul_le_mul_of_nonneg_left hxnorm (norm_nonneg T))

/-- The rank-one maps δₖ ⊗ 1_U in the finite-neighborhood projection are compact. -/
theorem isCompactOperator_smulRight (φ : E →L[𝕜] 𝕜) (v : F) :
    IsCompactOperator (φ.smulRight v) := by
  have hle : LinearMap.range (φ.smulRight v).toLinearMap ≤ 𝕜 ∙ v := by
    rintro y ⟨x, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hfinite : FiniteDimensional 𝕜 (LinearMap.range (φ.smulRight v).toLinearMap) :=
    FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)
  exact isCompactOperator_of_finiteRank _ hfinite

end JLMS
