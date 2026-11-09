import BanachIsometric.InjectiveFrameProjection

/-! Genuine graph coordinates over a real subspace U. The graph frame sends
x to x+A x in the original ambient Euclidean space. Its orthogonal projector
is the proved analytic frame formula, with actual range and dimension. -/

noncomputable section
namespace BanachIsometric
open Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

def subspaceGraphFrame (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) : U →L[ℝ] V :=
  U.subtypeL + Uᗮ.subtypeL.comp A

omit [FiniteDimensional ℝ V] in
@[simp] theorem subspaceGraphFrame_apply (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) (x : U) :
    subspaceGraphFrame U A x = (x : V) + (A x : V) := rfl

@[simp] theorem orthogonalProjection_subspaceGraphFrame
    (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) (x : U) :
    U.orthogonalProjection (subspaceGraphFrame U A x) = x := by
  rw [subspaceGraphFrame_apply, map_add,
    Submodule.orthogonalProjection_mem_subspace_eq_self,
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero (A x).property,
    add_zero]

@[simp] theorem orthogonalProjection_orthogonal_subspaceGraphFrame
    (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) (x : U) :
    Uᗮ.orthogonalProjection (subspaceGraphFrame U A x) = A x := by
  rw [subspaceGraphFrame_apply, map_add,
    Submodule.orthogonalProjection_orthogonal_apply_eq_zero x.property,
    Submodule.orthogonalProjection_mem_subspace_eq_self, zero_add]

theorem subspaceGraphFrame_injective (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    Function.Injective (subspaceGraphFrame U A) := by
  intro x y hxy
  have h := congrArg U.orthogonalProjection hxy
  simpa only [orthogonalProjection_subspaceGraphFrame] using h

theorem subspaceGraphFrame_adjoint_subtype (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    (subspaceGraphFrame U A).adjoint.comp U.subtypeL = ContinuousLinearMap.id ℝ U := by
  have h : U.orthogonalProjection.comp (subspaceGraphFrame U A) = ContinuousLinearMap.id ℝ U := by
    apply ContinuousLinearMap.ext
    intro x
    exact orthogonalProjection_subspaceGraphFrame U A x
  have h' := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp, U.adjoint_orthogonalProjection,
    ContinuousLinearMap.adjoint_id] using h'

def subspaceGraphProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) : V →L[ℝ] V :=
  frameProjection (subspaceGraphFrame U A)

def subspaceGraph (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) : Submodule ℝ V :=
  LinearMap.range (subspaceGraphFrame U A).toLinearMap

theorem subspaceGraphProjection_eq_starProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    subspaceGraphProjection U A = (subspaceGraph U A).starProjection :=
  frameProjection_eq_starProjection _ (subspaceGraphFrame_injective U A)

theorem subspaceGraph_finrank (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    Module.finrank ℝ (subspaceGraph U A) = Module.finrank ℝ U :=
  LinearMap.finrank_range_of_inj (subspaceGraphFrame_injective U A)

theorem subspaceGraphProjection_isStarProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    IsStarProjection (subspaceGraphProjection U A) :=
  frameProjection_isStarProjection _ (subspaceGraphFrame_injective U A)

theorem subspaceGraphProjection_range (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    LinearMap.range (subspaceGraphProjection U A).toLinearMap = subspaceGraph U A :=
  frameProjection_range _ (subspaceGraphFrame_injective U A)

def graphGrassmannianProjection {d : ℕ} (U : RealGrassmannian V d)
    (A : U.val →L[ℝ] U.valᗮ) : ProjectionGrassmannian V d :=
  ⟨subspaceGraphProjection U.val A, subspaceGraphProjection_isStarProjection _ _, by
    rw [subspaceGraphProjection_range]
    exact (subspaceGraph_finrank U.val A).trans U.property⟩

omit [FiniteDimensional ℝ V] in
theorem contDiff_subspaceGraphFrame (U : Submodule ℝ V) :
    ContDiff ℝ ⊤ (subspaceGraphFrame U) :=
  contDiff_const.add (contDiff_const.clm_comp contDiff_id)

theorem contDiff_subspaceGraphProjection (U : Submodule ℝ V) :
    ContDiff ℝ ⊤ (subspaceGraphProjection U) := by
  apply contDiff_iff_contDiffAt.mpr
  intro A
  exact (contDiffAt_frameProjection _ (subspaceGraphFrame_injective U A)).comp A
    (contDiff_subspaceGraphFrame U).contDiffAt

theorem continuous_graphGrassmannianProjection {d : ℕ} (U : RealGrassmannian V d) :
    Continuous (graphGrassmannianProjection U) :=
  (contDiff_subspaceGraphProjection U.val).continuous.subtype_mk _

def graphCompression (U : Submodule ℝ V) (P : V →L[ℝ] V) : U →L[ℝ] U :=
  U.orthogonalProjection.comp (P.comp U.subtypeL)

def graphCrossBlock (U : Submodule ℝ V) (P : V →L[ℝ] V) : U →L[ℝ] Uᗮ :=
  Uᗮ.orthogonalProjection.comp (P.comp U.subtypeL)

def graphCoordinate (U : Submodule ℝ V) (P : V →L[ℝ] V) : U →L[ℝ] Uᗮ :=
  (graphCrossBlock U P).comp (Ring.inverse (graphCompression U P))

theorem graphCompression_graphProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    graphCompression U (subspaceGraphProjection U A) = Ring.inverse (frameGram (subspaceGraphFrame U A)) := by
  apply ContinuousLinearMap.ext
  intro x
  change U.orthogonalProjection (subspaceGraphFrame U A
    (Ring.inverse (frameGram (subspaceGraphFrame U A)) ((subspaceGraphFrame U A).adjoint (x : V)))) = _
  rw [orthogonalProjection_subspaceGraphFrame]
  have h := congrArg (fun T : U →L[ℝ] U => T x) (subspaceGraphFrame_adjoint_subtype U A)
  change (subspaceGraphFrame U A).adjoint (x : V) = x at h
  rw [h]

theorem graphCompression_graphProjection_isUnit (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    IsUnit (graphCompression U (subspaceGraphProjection U A)) := by
  rw [graphCompression_graphProjection]
  exact (frameGram_isUnit _ (subspaceGraphFrame_injective U A)).ringInverse

theorem graphCrossBlock_graphProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    graphCrossBlock U (subspaceGraphProjection U A) =
      A.comp (graphCompression U (subspaceGraphProjection U A)) := by
  apply ContinuousLinearMap.ext
  intro x
  change Uᗮ.orthogonalProjection (subspaceGraphFrame U A
    (Ring.inverse (frameGram (subspaceGraphFrame U A)) ((subspaceGraphFrame U A).adjoint (x : V)))) = _
  rw [orthogonalProjection_orthogonal_subspaceGraphFrame]
  change A _ = A (U.orthogonalProjection (subspaceGraphFrame U A _))
  rw [orthogonalProjection_subspaceGraphFrame]
  rfl

theorem graphCoordinate_graphProjection (U : Submodule ℝ V) (A : U →L[ℝ] Uᗮ) :
    graphCoordinate U (subspaceGraphProjection U A) = A := by
  rw [graphCoordinate, graphCrossBlock_graphProjection, ContinuousLinearMap.comp_assoc]
  have hunit := graphCompression_graphProjection_isUnit U A
  have hcancel : (graphCompression U (subspaceGraphProjection U A)).comp
      (Ring.inverse (graphCompression U (subspaceGraphProjection U A))) = ContinuousLinearMap.id ℝ U :=
    Ring.mul_inverse_cancel _ hunit
  rw [hcancel, ContinuousLinearMap.comp_id]

theorem contDiff_graphCompression (U : Submodule ℝ V) : ContDiff ℝ ⊤ (graphCompression U) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem contDiff_graphCrossBlock (U : Submodule ℝ V) : ContDiff ℝ ⊤ (graphCrossBlock U) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem contDiffAt_graphCoordinate (U : Submodule ℝ V) (P : V →L[ℝ] V)
    (hunit : IsUnit (graphCompression U P)) : ContDiffAt ℝ ⊤ (graphCoordinate U) P := by
  have hInv : ContDiffAt ℝ ⊤ Ring.inverse (graphCompression U P) := by
    simpa only [hunit.unit_spec] using (contDiffAt_ringInverse (R := U →L[ℝ] U) ℝ hunit.unit :
      ContDiffAt ℝ ⊤ Ring.inverse (hunit.unit : U →L[ℝ] U))
  exact (contDiff_graphCrossBlock U).contDiffAt.clm_comp
    (hInv.comp P (contDiff_graphCompression U).contDiffAt)

end BanachIsometric
