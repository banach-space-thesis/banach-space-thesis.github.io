import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The real d-subspace Grassmannian is faithfully represented by actual
self-adjoint idempotent operators of range dimension d. The topology is the
operator-gap metric, with the original Euclidean norm unchanged. This is the
subspace convention; Mathlib's ring-theoretic Grassmannian instead indexes
locally free quotient rank and has no manifold structure at this revision. -/

noncomputable section
namespace BanachIsometric

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

abbrev RealGrassmannian (d : ℕ) := {U : Submodule ℝ V // Module.finrank ℝ U = d}

abbrev ProjectionGrassmannian (d : ℕ) :=
  {P : V →L[ℝ] V // IsStarProjection P ∧ Module.finrank ℝ (LinearMap.range P.toLinearMap) = d}

def realGrassmannianProjection (d : ℕ) (U : RealGrassmannian V d) : ProjectionGrassmannian V d :=
  ⟨U.val.starProjection, isStarProjection_starProjection,
    by
      have hr : LinearMap.range U.val.starProjection.toLinearMap = U.val :=
        Submodule.range_starProjection U.val
      rw [hr]
      exact U.property⟩

def projectionGrassmannianRange (d : ℕ) (P : ProjectionGrassmannian V d) : RealGrassmannian V d :=
  ⟨LinearMap.range P.val.toLinearMap, P.property.2⟩

def realGrassmannianProjectionEquiv (d : ℕ) : RealGrassmannian V d ≃ ProjectionGrassmannian V d where
  toFun := realGrassmannianProjection V d
  invFun := projectionGrassmannianRange V d
  left_inv U := by
    apply Subtype.ext
    exact Submodule.range_starProjection U.val
  right_inv P := by
    apply Subtype.ext
    exact (ContinuousLinearMap.IsStarProjection.ext
      isStarProjection_starProjection P.property.1 (Submodule.range_starProjection _))

instance realGrassmannianMetricSpace (d : ℕ) : MetricSpace (RealGrassmannian V d) :=
  MetricSpace.induced (realGrassmannianProjection V d) (realGrassmannianProjectionEquiv V d).injective
    inferInstance

def realGrassmannianProjectionIsometry (d : ℕ) : RealGrassmannian V d ≃ᵢ ProjectionGrassmannian V d :=
  { realGrassmannianProjectionEquiv V d with isometry_toFun := fun _ _ => rfl }

@[simp] theorem realGrassmannian_dist (d : ℕ) (U W : RealGrassmannian V d) :
    dist U W = ‖U.val.starProjection - W.val.starProjection‖ := by
  change dist U.val.starProjection W.val.starProjection = _
  exact dist_eq_norm _ _

@[simp] theorem projectionGrassmannian_range_projection (d : ℕ) (U : RealGrassmannian V d) :
    projectionGrassmannianRange V d (realGrassmannianProjection V d U) = U :=
  (realGrassmannianProjectionEquiv V d).left_inv U

@[simp] theorem realGrassmannian_projection_range (d : ℕ) (P : ProjectionGrassmannian V d) :
    realGrassmannianProjection V d (projectionGrassmannianRange V d P) = P :=
  (realGrassmannianProjectionEquiv V d).right_inv P

end BanachIsometric
