import BanachIsometric.HermitianDeletionHyperplanes
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Trace of actual orthogonal compressions of represented real forms

The compressed Riesz operator is derived from the restricted bilinear form.
Trace cyclicity and an explicit rank-one formula for the normal projection
then compute the trace removed by a geometric section.
-/

namespace BanachIsometric

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem relativeOperator_restrict_eq_orthogonalCompression
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (H : Submodule ℝ E) :
    hermitianRelativeOperator (restrictSesqForm B H) =
      H.orthogonalProjection.toLinearMap.comp ((hermitianRelativeOperator B).comp H.subtype) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [hermitianRelativeOperator_inner]
  change B x.val y.val = inner ℝ (H.orthogonalProjection (hermitianRelativeOperator B x.val)) y
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_right, hermitianRelativeOperator_inner]

theorem trace_relativeOperator_restrict_eq_compression
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (H : Submodule ℝ E) :
    LinearMap.trace ℝ H (hermitianRelativeOperator (restrictSesqForm B H)) =
      LinearMap.trace ℝ E (H.starProjection.toLinearMap.comp (hermitianRelativeOperator B)) := by
  rw [relativeOperator_restrict_eq_orthogonalCompression, ← LinearMap.comp_assoc]
  have h := LinearMap.trace_comp_comm' H.subtype
    (H.orthogonalProjection.toLinearMap.comp (hermitianRelativeOperator B))
  exact h

theorem trace_relativeOperator_restrict_eq_sub_rank_one
    {ι : Type*} [Fintype ι]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (H : Submodule ℝ E) (v : ι → E)
    (hprojection : H.starProjection.toLinearMap = LinearMap.id -
      ∑ i, (innerₗ E (v i)).smulRight (v i)) :
    LinearMap.trace ℝ H (hermitianRelativeOperator (restrictSesqForm B H)) =
      LinearMap.trace ℝ E (hermitianRelativeOperator B) - ∑ i, B (v i) (v i) := by
  classical
  have hs : (∑ i, (innerₗ E (v i)).smulRight (v i)).comp (hermitianRelativeOperator B) =
      ∑ i, ((innerₗ E (v i)).smulRight (v i)).comp (hermitianRelativeOperator B) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [trace_relativeOperator_restrict_eq_compression, hprojection, LinearMap.sub_comp,
    LinearMap.id_comp, map_sub, hs, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : ((innerₗ E (v i)).smulRight (v i)).comp (hermitianRelativeOperator B) =
      ((innerₗ E (v i)).comp (hermitianRelativeOperator B)).smulRight (v i) := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight]
  change inner ℝ (v i) (hermitianRelativeOperator B (v i)) = B (v i) (v i)
  exact inner_hermitianRelativeOperator B (fun x y => hB x y) _ _

end

end BanachIsometric
