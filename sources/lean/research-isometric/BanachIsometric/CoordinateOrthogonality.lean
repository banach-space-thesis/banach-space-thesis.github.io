import BanachIsometric.Covariance
import BanachIsometric.OrthogonalStabilizer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix

/-!
# Euclidean bodies and orthogonal matrices in coordinate norm

The canonical coordinate map is a continuous linear equivalence from genuine
Euclidean space to the ordinary finite Pi space. The latter retains its sup
norm. Euclidean isometries become actual orthogonal matrices, and the matrix
action agrees exactly with transport of the original vectors and bodies.
-/

namespace BanachIsometric

open MeasureTheory Set

noncomputable section

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

/-- A linear equivalence between two bodies in the same covariance position
preserves the original inner product. The bodies need not coincide. -/
theorem covariancePosition_inner_map_between (μ : Measure G) [μ.IsAddHaarMeasure]
    {S T : Set G} (hS : IsCompact S)
    (hCS : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (hCT : covarianceOperator μ T = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = T) (x y : G) :
    inner ℝ (e x) (e y) = inner ℝ x y := by
  have htransport := covarianceOperator_image μ hS e
  rw [he, hCS, hCT] at htransport
  have hright : e.toContinuousLinearMap.comp e.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ G := by
    simpa only [ContinuousLinearMap.id_comp] using htransport.symm
  have hadj : ∀ z, e.toContinuousLinearMap.adjoint z = e.symm z := by
    intro z
    apply e.injective
    rw [e.apply_symm_apply]
    exact congrArg (fun A : G →L[ℝ] G => A z) hright
  calc
    inner ℝ (e x) (e y) = inner ℝ x (e.toContinuousLinearMap.adjoint (e y)) :=
      (ContinuousLinearMap.adjoint_inner_right e.toContinuousLinearMap x (e y)).symm
    _ = inner ℝ x y := by rw [hadj, e.symm_apply_apply]

def covariancePositionIsometryBetween (μ : Measure G) [μ.IsAddHaarMeasure]
    {S T : Set G} (hS : IsCompact S)
    (hCS : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (hCT : covarianceOperator μ T = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = T) : G ≃ₗᵢ[ℝ] G :=
  e.toLinearEquiv.isometryOfInner (covariancePosition_inner_map_between μ hS hCS hCT e he)

@[simp] theorem covariancePositionIsometryBetween_apply (μ : Measure G) [μ.IsAddHaarMeasure]
    {S T : Set G} (hS : IsCompact S)
    (hCS : covarianceOperator μ S = ContinuousLinearMap.id ℝ G)
    (hCT : covarianceOperator μ T = ContinuousLinearMap.id ℝ G)
    (e : G ≃L[ℝ] G) (he : e '' S = T) (x : G) :
    covariancePositionIsometryBetween μ hS hCS hCT e he x = e x := rfl

/-- Coordinates preserve the real linear and topological structures. The
source has the Euclidean norm, and the target has its ordinary Pi sup norm. -/
def euclideanCoordinates (m : ℕ) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
  EuclideanSpace.equiv (Fin m) ℝ

@[simp] theorem euclideanCoordinates_apply (m : ℕ)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) : euclideanCoordinates m x i = x i := rfl

@[simp] theorem euclideanCoordinates_symm_apply (m : ℕ) (x : Fin m → ℝ) :
    (euclideanCoordinates m).symm x = WithLp.toLp 2 x := rfl

def coordinateBody {m : ℕ} (S : Set (EuclideanSpace ℝ (Fin m))) : Set (Fin m → ℝ) :=
  euclideanCoordinates m '' S

theorem isCompact_coordinateBody {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : IsCompact S) : IsCompact (coordinateBody S) :=
  hS.image (euclideanCoordinates m).continuous

/-- The actual orthogonal matrix of a Euclidean real linear isometry, in the
canonical orthonormal basis. No inner product is installed on the Pi target. -/
def euclideanIsometryMatrix {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    Matrix.orthogonalGroup (Fin m) ℝ := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  refine ⟨LinearMap.toMatrix b.toBasis b.toBasis e.toLinearMap, ?_⟩
  convert b.toMatrix_orthonormalBasis_mem_orthogonal (b.map e) using 1
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.map_apply]
  rfl

theorem euclideanIsometryMatrix_mulVec {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    (euclideanIsometryMatrix e : Matrix (Fin m) (Fin m) ℝ).mulVec
        (euclideanCoordinates m x) = euclideanCoordinates m (e x) := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have h := e.toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis x
  have hc (y : EuclideanSpace ℝ (Fin m)) :
      (b.toBasis.repr y : Fin m → ℝ) = euclideanCoordinates m y := by
    funext i
    exact b.coe_toBasis_repr_apply y i
  rw [hc x] at h
  exact h.trans (hc (e.toLinearEquiv x))

theorem euclideanIsometryMatrix_image {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m))) :
    (euclideanIsometryMatrix e : Matrix (Fin m) (Fin m) ℝ).mulVec '' coordinateBody S =
      coordinateBody (e '' S) := by
  unfold coordinateBody
  rw [image_image, image_image]
  congr 1
  funext x
  exact euclideanIsometryMatrix_mulVec e x

/-- Actual linearly equivalent covariance-normalized Euclidean bodies give
orthogonal images of their exact coordinate bodies. -/
theorem exists_orthogonal_coordinate_image_of_covariancePosition {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {S T : Set (EuclideanSpace ℝ (Fin m))} (hS : IsCompact S)
    (hCS : covarianceOperator μ S = ContinuousLinearMap.id ℝ _)
    (hCT : covarianceOperator μ T = ContinuousLinearMap.id ℝ _)
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) (he : e '' S = T) :
    ∃ Q : Matrix.orthogonalGroup (Fin m) ℝ,
      (Q : Matrix (Fin m) (Fin m) ℝ).mulVec '' coordinateBody S = coordinateBody T := by
  let f := covariancePositionIsometryBetween μ hS hCS hCT e he
  refine ⟨euclideanIsometryMatrix f, ?_⟩
  have h := euclideanIsometryMatrix_image f S
  have hfe : (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) = e := rfl
  simpa only [hfe, he] using h

open scoped Matrix.Norms.Operator

/-- Matrix operators on the original Euclidean space, as a continuous linear
map of the ambient operator-norm matrix space. -/
def matrixEuclideanOperator (m : ℕ) : Matrix (Fin m) (Fin m) ℝ →L[ℝ]
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (Matrix.toEuclideanLin M).toContinuousLinearMap
      map_add' := by
        intro M N
        apply ContinuousLinearMap.ext
        intro x
        simp only [map_add, ContinuousLinearMap.add_apply]
      map_smul' := by
        intro t M
        apply ContinuousLinearMap.ext
        intro x
        simp only [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply] }

theorem matrixEuclideanOperator_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    matrixEuclideanOperator m M x =
      (euclideanCoordinates m).symm (M.mulVec (euclideanCoordinates m x)) := rfl

/-- An actual orthogonal matrix acts as a real continuous linear equivalence
on the original Euclidean space by the exact coordinate conjugation. -/
def orthogonalEuclideanEquiv {m : ℕ} (Q : Matrix.orthogonalGroup (Fin m) ℝ) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (euclideanCoordinates m).trans
    ((Matrix.UnitaryGroup.toLinearEquiv Q).toContinuousLinearEquiv.trans
      (euclideanCoordinates m).symm)

@[simp] theorem orthogonalEuclideanEquiv_toContinuousLinearMap {m : ℕ}
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) :
    (orthogonalEuclideanEquiv Q).toContinuousLinearMap =
      matrixEuclideanOperator m (Q : Matrix (Fin m) (Fin m) ℝ) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

@[simp] theorem orthogonalEuclideanEquiv_one (m : ℕ) :
    orthogonalEuclideanEquiv (1 : Matrix.orthogonalGroup (Fin m) ℝ) =
      ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin m)) := by
  apply ContinuousLinearEquiv.ext
  funext x
  change (euclideanCoordinates m).symm
    ((1 : Matrix (Fin m) (Fin m) ℝ).mulVec (euclideanCoordinates m x)) = x
  rw [Matrix.one_mulVec, ContinuousLinearEquiv.symm_apply_apply]

theorem coordinateBody_orthogonalEuclideanEquiv_image {m : ℕ}
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) (S : Set (EuclideanSpace ℝ (Fin m))) :
    coordinateBody (orthogonalEuclideanEquiv Q '' S) =
      (Q : Matrix (Fin m) (Fin m) ℝ).mulVec '' coordinateBody S := by
  unfold coordinateBody
  rw [image_image, image_image]
  congr 1

theorem orthogonalEuclideanEquiv_image_iff {m : ℕ}
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) (S T : Set (EuclideanSpace ℝ (Fin m))) :
    orthogonalEuclideanEquiv Q '' S = T ↔
      (Q : Matrix (Fin m) (Fin m) ℝ).mulVec '' coordinateBody S = coordinateBody T := by
  rw [← coordinateBody_orthogonalEuclideanEquiv_image]
  exact (Set.image_injective.mpr (euclideanCoordinates m).injective).eq_iff.symm

end
end BanachIsometric
