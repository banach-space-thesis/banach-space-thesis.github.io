import BanachIsometric.StabilizerComponents
import BanachIsometric.ExactSectionBundle
import BanachIsometric.NormalizedImageMoments
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The actual operator-unit body group and its finite component quotient

In covariance position, every actual body automorphism is Euclidean isometric.
The exact coordinate operators identify the body's operator-unit subgroup with
its orthogonal-matrix subgroup by a continuous group isomorphism. Thus the
finite-component theorem applies to the structure group used by the actual
exact-section bundle, with its original operator-unit topology.
-/

noncomputable section

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology Matrix.Norms.Operator

variable {m : ℕ}

theorem euclideanOperatorMatrix_mulVec
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) (x : Fin m → ℝ) :
    (euclideanOperatorMatrix m T).mulVec x =
      euclideanCoordinates m (T ((euclideanCoordinates m).symm x)) := by
  change (LinearMap.toMatrix' _).mulVec x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem euclideanIsometryMatrix_eq_operatorMatrix
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    (euclideanIsometryMatrix e : Matrix (Fin m) (Fin m) ℝ) =
      euclideanOperatorMatrix m e.toContinuousLinearMap := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (euclideanIsometryMatrix e : Matrix (Fin m) (Fin m) ℝ).mulVec x =
    (euclideanOperatorMatrix m e.toContinuousLinearMap).mulVec x
  rw [euclideanOperatorMatrix_mulVec]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    euclideanIsometryMatrix_mulVec e ((euclideanCoordinates m).symm x)

theorem euclideanOperatorMatrix_matrixEuclideanOperator
    (M : Matrix (Fin m) (Fin m) ℝ) :
    euclideanOperatorMatrix m (matrixEuclideanOperator m M) = M := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (euclideanOperatorMatrix m (matrixEuclideanOperator m M)).mulVec x = M.mulVec x
  rw [euclideanOperatorMatrix_mulVec, matrixEuclideanOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem matrixEuclideanOperator_euclideanOperatorMatrix
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    matrixEuclideanOperator m (euclideanOperatorMatrix m T) = T := by
  ext x
  rw [matrixEuclideanOperator_apply, euclideanOperatorMatrix_mulVec,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem euclideanOperatorMatrix_mul
    (T U : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    euclideanOperatorMatrix m (T * U) = euclideanOperatorMatrix m T * euclideanOperatorMatrix m U := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (euclideanOperatorMatrix m (T * U)).mulVec x =
    (euclideanOperatorMatrix m T * euclideanOperatorMatrix m U).mulVec x
  rw [← Matrix.mulVec_mulVec, euclideanOperatorMatrix_mulVec,
    euclideanOperatorMatrix_mulVec, euclideanOperatorMatrix_mulVec,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

section BodyGroups

variable (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hC : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)

def bodyAutomorphismToOrthogonal (g : bodyAutomorphismGroup S) :
    orthogonalBodyStabilizerSubgroup m (coordinateBody S) := by
  let e := ContinuousLinearEquiv.ofUnit g.val
  let f := covariancePositionIsometry μ hS hC e g.property
  refine ⟨euclideanIsometryMatrix f, ?_⟩
  change (euclideanIsometryMatrix f : Matrix (Fin m) (Fin m) ℝ).mulVec '' coordinateBody S = _
  rw [euclideanIsometryMatrix_image]
  change coordinateBody (e '' S) = coordinateBody S
  exact congrArg coordinateBody g.property

def orthogonalToBodyAutomorphism
    (Q : orthogonalBodyStabilizerSubgroup m (coordinateBody S)) : bodyAutomorphismGroup S :=
  ⟨(orthogonalEuclideanEquiv Q.val).toUnit,
    (orthogonalEuclideanEquiv_image_iff Q.val S S).mpr Q.property⟩

theorem bodyAutomorphismToOrthogonal_matrix (g : bodyAutomorphismGroup S) :
    ((bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC) g).val : Matrix (Fin m) (Fin m) ℝ) =
      euclideanOperatorMatrix m (g.val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) := by
  exact euclideanIsometryMatrix_eq_operatorMatrix _

/-- The exact group isomorphism between the actual structure group of the
exact-section bundle and the coordinate orthogonal body stabiliser. -/
def bodyAutomorphismOrthogonalMulEquiv :
    bodyAutomorphismGroup S ≃* orthogonalBodyStabilizerSubgroup m (coordinateBody S) where
  toFun := bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC)
  invFun := orthogonalToBodyAutomorphism S
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    change (orthogonalEuclideanEquiv (bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC) g).val).toContinuousLinearMap = _
    rw [orthogonalEuclideanEquiv_toContinuousLinearMap,
      bodyAutomorphismToOrthogonal_matrix, matrixEuclideanOperator_euclideanOperatorMatrix]
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    rw [bodyAutomorphismToOrthogonal_matrix]
    change euclideanOperatorMatrix m (orthogonalEuclideanEquiv Q.val).toContinuousLinearMap = _
    rw [orthogonalEuclideanEquiv_toContinuousLinearMap,
      euclideanOperatorMatrix_matrixEuclideanOperator]
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    rw [bodyAutomorphismToOrthogonal_matrix]
    change euclideanOperatorMatrix m
      ((g.val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) *
        (h.val : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) = _
    rw [euclideanOperatorMatrix_mul, ← bodyAutomorphismToOrthogonal_matrix (μ := μ) (S := S) (hS := hS) (hC := hC) g,
      ← bodyAutomorphismToOrthogonal_matrix (μ := μ) (S := S) (hS := hS) (hC := hC) h]
    rfl

theorem continuous_bodyAutomorphismToOrthogonal :
    Continuous (bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hf := (euclideanOperatorMatrix m).continuous.comp
    (Units.continuous_val.comp (continuous_subtype_val (p := fun g => g ∈ bodyAutomorphismGroup S)))
  apply hf.congr
  intro g
  exact (bodyAutomorphismToOrthogonal_matrix (μ := μ) (S := S) (hS := hS) (hC := hC) g).symm

theorem continuous_orthogonalToBodyAutomorphism : Continuous (orthogonalToBodyAutomorphism S) := by
  apply Continuous.subtype_mk
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  change Continuous (fun Q : orthogonalBodyStabilizerSubgroup m (coordinateBody S) =>
    (orthogonalEuclideanEquiv Q.val).toContinuousLinearMap)
  simp_rw [orthogonalEuclideanEquiv_toContinuousLinearMap]
  exact (matrixEuclideanOperator m).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The group isomorphism retains the actual operator-unit topology on the
left and the actual matrix-subgroup topology on the right. -/
def bodyAutomorphismOrthogonalHomeomorph :
    bodyAutomorphismGroup S ≃ₜ orthogonalBodyStabilizerSubgroup m (coordinateBody S) where
  toEquiv := (bodyAutomorphismOrthogonalMulEquiv (μ := μ) (S := S) (hS := hS) (hC := hC)).toEquiv
  continuous_toFun := continuous_bodyAutomorphismToOrthogonal (μ := μ) (S := S) (hS := hS) (hC := hC)
  continuous_invFun := continuous_orthogonalToBodyAutomorphism S

include μ hS hC

/-- Covariance position makes the actual operator-unit body group compact. -/
theorem compactSpace_bodyAutomorphismGroup : CompactSpace (bodyAutomorphismGroup S) := by
  letI := compactSpace_orthogonalBodyStabilizerSubgroup m (isCompact_coordinateBody hS).isClosed
  exact (bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)).symm.compactSpace

/-- The exact topological group identification preserves the connected
component of the identity, including its actual subgroup topology. -/
theorem bodyAutomorphismOrthogonal_preimage_connectedComponent :
    (bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)) ⁻¹'
      (Subgroup.connectedComponentOfOne
        (orthogonalBodyStabilizerSubgroup m (coordinateBody S)) : Set _) =
      (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) : Set _) := by
  let e := bodyAutomorphismOrthogonalHomeomorph (μ := μ) (S := S) (hS := hS) (hC := hC)
  have he1 : e 1 = 1 := (bodyAutomorphismOrthogonalMulEquiv
    (μ := μ) (S := S) (hS := hS) (hC := hC)).map_one
  have hes1 : e.symm 1 = 1 := by
    apply e.injective
    rw [e.apply_symm_apply, he1]
  ext g
  change e g ∈ connectedComponent (1 : orthogonalBodyStabilizerSubgroup m (coordinateBody S)) ↔
    g ∈ connectedComponent (1 : bodyAutomorphismGroup S)
  constructor
  · intro hg
    have h := e.symm.continuous.mapsTo_connectedComponent (e 1)
    rw [he1] at h
    simpa only [e.symm_apply_apply, hes1] using h hg
  · intro hg
    have h := e.continuous.mapsTo_connectedComponent 1 hg
    simpa only [he1] using h

/-- The identity component of the actual operator-unit structure group is
open. The only body assumptions are compactness, regular closedness, positive
Haar mass, and actual covariance position. -/
theorem isOpen_bodyAutomorphismGroup_connectedComponent
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    IsOpen (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S) :
      Set (bodyAutomorphismGroup S)) := by
  let G := orthogonalBodyStabilizerSubgroup m (coordinateBody S)
  let N := Subgroup.connectedComponentOfOne G
  letI := coordinateMeasure_isAddHaarMeasure μ
  have hcoord : coordinateMeasure μ (coordinateBody S) ≠ 0 := by
    rwa [coordinateMeasure_coordinateBody]
  letI : Finite (G ⧸ N) := finite_orthogonalBodyStabilizer_componentQuotient
    (coordinateMeasure μ) (coordinateBody S) (isCompact_coordinateBody hS)
    (coordinateBody_regularClosed hreg) hcoord
  letI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hopen : IsOpen (N : Set G) :=
    N.isOpen_of_isClosed_of_finiteIndex isClosed_connectedComponent
  rw [← bodyAutomorphismOrthogonal_preimage_connectedComponent
    (μ := μ) (S := S) (hS := hS) (hC := hC)]
  exact hopen.preimage (bodyAutomorphismOrthogonalHomeomorph
    (μ := μ) (S := S) (hS := hS) (hC := hC)).continuous

/-- The actual structure group of the exact-section bundle has finitely
many connected components in its original operator-unit topology. -/
theorem finite_bodyAutomorphismGroup_componentQuotient
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    Finite ((bodyAutomorphismGroup S) ⧸
      Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) := by
  letI := compactSpace_bodyAutomorphismGroup (μ := μ) (S := S) (hS := hS) (hC := hC)
  exact Subgroup.quotient_finite_of_isOpen _
    (isOpen_bodyAutomorphismGroup_connectedComponent
      (μ := μ) (S := S) (hS := hS) (hC := hC) hreg h0)

end BodyGroups

end BanachIsometric
