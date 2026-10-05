import JLMS.CZeroTools
import JLMS.FiniteRank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Section 4: finite-neighborhood projections

A supplied finite family of disjoint compact clopen neighborhoods defines
P f = ∑ᵢ f(pᵢ) 1_{Uᵢ}. This module proves its projection identity, norm estimates,
finite-dimensional range, and adjoint action on the evaluation functionals.
Existence of such neighborhoods from scatteredness is proved separately in
ScatteredTopology.lean.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]
variable {ι : Type*} [Fintype ι]

/-- The paper's disjoint neighborhood collection, indexed by its finite points. -/
structure NeighborhoodFamily (p : ι → K) where
  sets : ι → Set K
  clopen : ∀ i, IsClopen (sets i)
  compact : ∀ i, IsCompact (sets i)
  contains : ∀ i, p i ∈ sets i
  disjoint : Pairwise fun i j => Disjoint (sets i) (sets j)

variable {p : ι → K} (U : NeighborhoodFamily p)

/-- P = ∑ δ_{pᵢ} ⊗ 1_{Uᵢ}. -/
def neighborhoodProjection : CZero 𝕜 K →L[𝕜] CZero 𝕜 K :=
  ∑ i, (evaluation (𝕜 := 𝕜) (p i)).smulRight
    (clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i))

theorem neighborhoodProjection_apply (f : CZero 𝕜 K) :
    neighborhoodProjection U f =
      ∑ i, f (p i) • clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i) := by
  simp [neighborhoodProjection]

omit [Fintype ι] in
theorem indicator_at_point (i j : ι) :
    clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i) (p j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [U.contains i]
  · have hnot : p j ∉ U.sets i := fun hi =>
      Set.disjoint_left.mp (U.disjoint hij) hi (U.contains j)
    simp [hij, hnot]

/-- P reproduces f at every selected point. -/
@[simp] theorem neighborhoodProjection_at_point (f : CZero 𝕜 K) (j : ι) :
    neighborhoodProjection U f (p j) = f (p j) := by
  have h := congrArg (evaluation (𝕜 := 𝕜) (p j)) (neighborhoodProjection_apply U f)
  simp only [map_sum, map_smul, evaluation_apply, smul_eq_mul] at h
  rw [h]
  simp_rw [indicator_at_point]
  simp

theorem neighborhoodProjection_idempotent :
    (neighborhoodProjection (𝕜 := 𝕜) U).comp (neighborhoodProjection U) =
      neighborhoodProjection U := by
  apply ContinuousLinearMap.ext
  intro f
  change neighborhoodProjection U (neighborhoodProjection U f) = neighborhoodProjection U f
  rw [neighborhoodProjection_apply U (neighborhoodProjection U f)]
  simp only [neighborhoodProjection_at_point]
  exact (neighborhoodProjection_apply U f).symm

/-- Disjointness ensures at most one term contributes at any point. -/
theorem neighborhoodProjection_norm_apply_le (f : CZero 𝕜 K) :
    ‖neighborhoodProjection U f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖neighborhoodProjection U f x‖ ≤ ‖f‖
  have h := congrArg (evaluation (𝕜 := 𝕜) x) (neighborhoodProjection_apply U f)
  simp only [map_sum, map_smul, evaluation_apply, smul_eq_mul] at h
  rw [h]
  by_cases hx : ∃ i, x ∈ U.sets i
  · obtain ⟨i, hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simpa [hi] using norm_CZero_apply_le f (p i)
    · intro j _ hji
      have hj : x ∉ U.sets j := fun hj => Set.disjoint_left.mp (U.disjoint hji) hj hi
      simp [hj]
    · simp
  · push_neg at hx
    simp [hx, norm_nonneg f]

theorem neighborhoodProjection_norm_le : ‖neighborhoodProjection (𝕜 := 𝕜) U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using neighborhoodProjection_norm_apply_le U f

/-- The range lies in the span of the finitely many neighborhood indicators. -/
theorem neighborhoodProjection_range_le :
    LinearMap.range (neighborhoodProjection (𝕜 := 𝕜) U).toLinearMap ≤
      Submodule.span 𝕜 (Set.range fun i =>
        clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i)) := by
  rintro g ⟨f, rfl⟩
  rw [ContinuousLinearMap.coe_coe, neighborhoodProjection_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem neighborhoodProjection_finiteRank :
    FiniteDimensional 𝕜 (LinearMap.range (neighborhoodProjection (𝕜 := 𝕜) U).toLinearMap) := by
  let W := Submodule.span 𝕜 (Set.range fun i =>
    clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i))
  letI : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (neighborhoodProjection_range_le U))
    (Submodule.inclusion_injective _)

theorem neighborhoodProjection_compact : IsCompactOperator (neighborhoodProjection (𝕜 := 𝕜) U) :=
  isCompactOperator_of_finiteRank _ (neighborhoodProjection_finiteRank U)

/-- Every selected point evaluation is fixed by the adjoint P*. -/
@[simp] theorem neighborhoodProjection_adjoint_evaluation (j : ι) :
    banachAdjoint (neighborhoodProjection (𝕜 := 𝕜) U) (evaluation (p j)) =
      evaluation (p j) := by
  ext f
  exact neighborhoodProjection_at_point U f j

/-- Empty index families give P = 0; nonempty families give norm exactly one. -/
theorem neighborhoodProjection_norm_eq_one [Nonempty ι] :
    ‖neighborhoodProjection (𝕜 := 𝕜) U‖ = 1 := by
  apply le_antisymm (neighborhoodProjection_norm_le U)
  obtain ⟨i⟩ := ‹Nonempty ι›
  let f := clopenIndicator (𝕜 := 𝕜) (U.sets i) (U.clopen i) (U.compact i)
  have hf : ‖f‖ = 1 := norm_clopenIndicator_eq_one _ _ _ ⟨p i, U.contains i⟩
  have hpoint := norm_CZero_apply_le (neighborhoodProjection U f) (p i)
  have hbound := (neighborhoodProjection (𝕜 := 𝕜) U).le_opNorm f
  have hone : f (p i) = 1 := by simp [f, U.contains i]
  rw [neighborhoodProjection_at_point, hone, norm_one] at hpoint
  rw [hf, mul_one] at hbound
  exact hpoint.trans hbound

/-- The factor-two estimate responsible for the constant in Theorem 1.6. -/
theorem norm_id_sub_neighborhoodProjection_le_two :
    ‖ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - neighborhoodProjection U‖ ≤ 2 := by
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := CZero 𝕜 K)
  have hnorm := norm_sub_le (ContinuousLinearMap.id 𝕜 (CZero 𝕜 K))
    (neighborhoodProjection (𝕜 := 𝕜) U)
  linarith [neighborhoodProjection_norm_le (𝕜 := 𝕜) U]

end JLMS
