import BanachIsometric.GrassmannianGraphProjection
import Mathlib.Topology.OpenPartialHomeomorph

/-! Actual open graph charts for the operator-gap Grassmannian. The source
condition is invertibility of the genuine orthogonal compression. All graph
maps are covered, and the two inverse identities are derived from actual
projection ranges and dimensions. Changes of graph coordinates are analytic. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem subspaceGraphFrame_coordinate_eq (U : Submodule ℝ V) (P : V →L[ℝ] V)
    (hunit : IsUnit (graphCompression U P)) :
    subspaceGraphFrame U (graphCoordinate U P) =
      P.comp (U.subtypeL.comp (Ring.inverse (graphCompression U P))) := by
  ext x
  let y := P ((Ring.inverse (graphCompression U P) x : U) : V)
  have hleft : U.orthogonalProjection y = x :=
    congrArg (fun T : U →L[ℝ] U => T x) (Ring.mul_inverse_cancel _ hunit)
  have hright : graphCoordinate U P x = Uᗮ.orthogonalProjection y := rfl
  have hdec : (U.orthogonalProjection y : V) + (Uᗮ.orthogonalProjection y : V) = y := by
    change U.starProjection y + Uᗮ.starProjection y = y
    rw [Submodule.starProjection_orthogonal_val]
    abel
  change (x : V) + (graphCoordinate U P x : V) = y
  rw [hright, ← hleft]
  exact hdec

theorem subspaceGraph_coordinate_eq_range (U : Submodule ℝ V) (P : V →L[ℝ] V)
    (hrank : Module.finrank ℝ (LinearMap.range P.toLinearMap) = Module.finrank ℝ U)
    (hunit : IsUnit (graphCompression U P)) :
    subspaceGraph U (graphCoordinate U P) = LinearMap.range P.toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨x, rfl⟩
    refine ⟨((Ring.inverse (graphCompression U P) x : U) : V), ?_⟩
    have h := congrArg (fun T : U →L[ℝ] V => T x) (subspaceGraphFrame_coordinate_eq U P hunit)
    exact h.symm
  · exact (subspaceGraph_finrank U (graphCoordinate U P)).trans hrank.symm

theorem subspaceGraphProjection_coordinate_eq (U : Submodule ℝ V) (P : V →L[ℝ] V)
    (hP : IsStarProjection P)
    (hrank : Module.finrank ℝ (LinearMap.range P.toLinearMap) = Module.finrank ℝ U)
    (hunit : IsUnit (graphCompression U P)) :
    subspaceGraphProjection U (graphCoordinate U P) = P := by
  apply ContinuousLinearMap.IsStarProjection.ext (subspaceGraphProjection_isStarProjection _ _) hP
  change LinearMap.range (subspaceGraphProjection U (graphCoordinate U P)).toLinearMap =
    LinearMap.range P.toLinearMap
  rw [subspaceGraphProjection_range]
  exact subspaceGraph_coordinate_eq_range U P hrank hunit

omit [FiniteDimensional ℝ V] in
theorem subspaceGraph_zero (U : Submodule ℝ V) : subspaceGraph U 0 = U := by
  ext y
  change (∃ x : U, subspaceGraphFrame U 0 x = y) ↔ y ∈ U
  simp only [subspaceGraphFrame_apply, ContinuousLinearMap.zero_apply, Submodule.coe_zero, add_zero]
  exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩

theorem subspaceGraphProjection_zero (U : Submodule ℝ V) :
    subspaceGraphProjection U 0 = U.starProjection := by
  rw [subspaceGraphProjection_eq_starProjection, subspaceGraph_zero]

def projectionGrassmannianGraphChart {d : ℕ} (U : RealGrassmannian V d) :
    OpenPartialHomeomorph (ProjectionGrassmannian V d) (U.val →L[ℝ] U.valᗮ) where
  toFun P := graphCoordinate U.val P.val
  invFun := graphGrassmannianProjection U
  source := {P | IsUnit (graphCompression U.val P.val)}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' A _ := graphCompression_graphProjection_isUnit U.val A
  left_inv' P hP := by
    apply Subtype.ext
    exact subspaceGraphProjection_coordinate_eq U.val P.val P.property.1
      (P.property.2.trans U.property.symm) hP
  right_inv' A _ := graphCoordinate_graphProjection U.val A
  open_source := (Units.isOpen (R := U.val →L[ℝ] U.val)).preimage
    ((contDiff_graphCompression U.val).continuous.comp continuous_subtype_val)
  open_target := isOpen_univ
  continuousOn_toFun P hP :=
    ((contDiffAt_graphCoordinate U.val P.val hP).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_graphGrassmannianProjection U).continuousOn

theorem projectionGrassmannianGraphChart_center_mem {d : ℕ} (U : RealGrassmannian V d) :
    realGrassmannianProjection V d U ∈ (projectionGrassmannianGraphChart U).source := by
  change IsUnit (graphCompression U.val U.val.starProjection)
  rw [← subspaceGraphProjection_zero]
  exact graphCompression_graphProjection_isUnit U.val 0

theorem projectionGrassmannianGraphChart_center {d : ℕ} (U : RealGrassmannian V d) :
    projectionGrassmannianGraphChart U (realGrassmannianProjection V d U) = 0 := by
  change graphCoordinate U.val U.val.starProjection = 0
  rw [← subspaceGraphProjection_zero]
  exact graphCoordinate_graphProjection U.val 0

def realGrassmannianGraphChart {d : ℕ} (U : RealGrassmannian V d) :
    OpenPartialHomeomorph (RealGrassmannian V d) (U.val →L[ℝ] U.valᗮ) :=
  (realGrassmannianProjectionIsometry V d).toHomeomorph.transOpenPartialHomeomorph
    (projectionGrassmannianGraphChart U)

theorem realGrassmannianGraphChart_center_mem {d : ℕ} (U : RealGrassmannian V d) :
    U ∈ (realGrassmannianGraphChart U).source :=
  projectionGrassmannianGraphChart_center_mem U

theorem realGrassmannianGraphChart_center {d : ℕ} (U : RealGrassmannian V d) :
    realGrassmannianGraphChart U U = 0 := projectionGrassmannianGraphChart_center U

theorem realGrassmannianGraphChart_symm_range {d : ℕ} (U : RealGrassmannian V d)
    (A : U.val →L[ℝ] U.valᗮ) :
    ((realGrassmannianGraphChart U).symm A).val = subspaceGraph U.val A :=
  subspaceGraphProjection_range U.val A

theorem realGrassmannianGraphChart_symm_projection {d : ℕ} (U : RealGrassmannian V d)
    (A : U.val →L[ℝ] U.valᗮ) :
    ((realGrassmannianGraphChart U).symm A).val.starProjection = subspaceGraphProjection U.val A := by
  exact congrArg Subtype.val (realGrassmannian_projection_range V d (graphGrassmannianProjection U A))

theorem projectionGrassmannian_graph_transition_contDiffOn {d : ℕ}
    (U W : RealGrassmannian V d) :
    ContDiffOn ℝ ⊤ ((projectionGrassmannianGraphChart U).symm.trans
      (projectionGrassmannianGraphChart W))
      ((projectionGrassmannianGraphChart U).symm.trans (projectionGrassmannianGraphChart W)).source := by
  intro A hA
  have hunit : IsUnit (graphCompression W.val (subspaceGraphProjection U.val A)) := hA.2
  exact ((contDiffAt_graphCoordinate W.val _ hunit).comp A
    (contDiff_subspaceGraphProjection U.val).contDiffAt).contDiffWithinAt

theorem realGrassmannian_graph_transition_contDiffOn {d : ℕ}
    (U W : RealGrassmannian V d) :
    ContDiffOn ℝ ⊤ ((realGrassmannianGraphChart U).symm.trans (realGrassmannianGraphChart W))
      ((realGrassmannianGraphChart U).symm.trans (realGrassmannianGraphChart W)).source := by
  have hfun : (((realGrassmannianGraphChart U).symm.trans (realGrassmannianGraphChart W)) :
      (U.val →L[ℝ] U.valᗮ) → (W.val →L[ℝ] W.valᗮ)) =
      fun A => graphCoordinate W.val (subspaceGraphProjection U.val A) := by
    funext A
    change graphCoordinate W.val (((realGrassmannianGraphChart U).symm A).val.starProjection) = _
    rw [realGrassmannianGraphChart_symm_projection]
  intro A hA
  have hunit := hA.2
  change IsUnit (graphCompression W.val
    (((realGrassmannianGraphChart U).symm A).val.starProjection)) at hunit
  rw [realGrassmannianGraphChart_symm_projection] at hunit
  rw [hfun]
  exact ((contDiffAt_graphCoordinate W.val _ hunit).comp A
    (contDiff_subspaceGraphProjection U.val).contDiffAt).contDiffWithinAt

end BanachIsometric
