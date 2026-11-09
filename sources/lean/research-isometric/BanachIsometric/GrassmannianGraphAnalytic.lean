import BanachIsometric.GrassmannianGraphChart

/-! The raw rational change between genuine graph models is analytic at
every point of its actual compression-unit domain. The point is kept as an
explicit graph-model variable for subsequent coordinate changes. -/

noncomputable section
namespace BanachIsometric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem contDiffAt_rawGrassmannianGraphTransition {d : ℕ}
    (U W : RealGrassmannian V d) (B : U.val →L[ℝ] U.valᗮ)
    (hunit : IsUnit (graphCompression W.val (subspaceGraphProjection U.val B))) :
    ContDiffAt ℝ ⊤ (fun A : U.val →L[ℝ] U.valᗮ =>
      graphCoordinate W.val (subspaceGraphProjection U.val A)) B :=
  ContDiffAt.comp (f := subspaceGraphProjection U.val) (g := graphCoordinate W.val) B
    (contDiffAt_graphCoordinate W.val _ hunit) (contDiff_subspaceGraphProjection U.val).contDiffAt

end BanachIsometric
