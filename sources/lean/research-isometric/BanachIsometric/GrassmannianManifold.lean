import BanachIsometric.GrassmannianGraphAnalytic
import BanachIsometric.AnalyticLinearCoordinates
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! An actual analytic Grassmannian manifold on the operator-gap topology.
The charts are genuine graph charts followed by honest continuous linear
changes to the explicit Euclidean model of dimension d(dim V-d). -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology Manifold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem grassmannian_graphModel_finrank {d : ℕ} (U : RealGrassmannian V d) :
    Module.finrank ℝ (U.val →L[ℝ] U.valᗮ) = d * (Module.finrank ℝ V - d) := by
  have horth : Module.finrank ℝ U.valᗮ = Module.finrank ℝ V - d := by
    have h := U.val.finrank_add_finrank_orthogonal
    rw [U.property] at h
    omega
  rw [← (LinearMap.toContinuousLinearMap :
    (U.val →ₗ[ℝ] U.valᗮ) ≃ₗ[ℝ] (U.val →L[ℝ] U.valᗮ)).finrank_eq]
  rw [Module.finrank_linearMap, U.property, horth]

abbrev GrassmannianModel (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) :=
  EuclideanSpace ℝ (Fin (d * (Module.finrank ℝ V - d)))

@[irreducible] def grassmannianModelCoordinate {d : ℕ} (U : RealGrassmannian V d) :
    (U.val →L[ℝ] U.valᗮ) ≃L[ℝ] GrassmannianModel V d :=
  (LinearEquiv.ofFinrankEq (U.val →L[ℝ] U.valᗮ) (GrassmannianModel V d)
    ((grassmannian_graphModel_finrank U).trans (finrank_euclideanSpace_fin).symm)).toContinuousLinearEquiv

def realGrassmannianStandardChart {d : ℕ} (U : RealGrassmannian V d) :
    OpenPartialHomeomorph (RealGrassmannian V d) (GrassmannianModel V d) :=
  (realGrassmannianGraphChart U).trans (grassmannianModelCoordinate U).toHomeomorph.toOpenPartialHomeomorph

theorem realGrassmannianStandardChart_apply {d : ℕ} (U W : RealGrassmannian V d) :
    realGrassmannianStandardChart U W =
      grassmannianModelCoordinate U (realGrassmannianGraphChart U W) := rfl

theorem realGrassmannianStandardChart_symm_apply {d : ℕ} (U : RealGrassmannian V d)
    (A : GrassmannianModel V d) :
    (realGrassmannianStandardChart U).symm A =
      (realGrassmannianGraphChart U).symm ((grassmannianModelCoordinate U).symm A) := rfl

def realGrassmannianChartedSpace (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) :
    ChartedSpace (GrassmannianModel V d) (RealGrassmannian V d) where
  atlas := range (realGrassmannianStandardChart (V := V) (d := d))
  chartAt := realGrassmannianStandardChart
  mem_chart_source U := ⟨realGrassmannianGraphChart_center_mem U, mem_univ _⟩
  chart_mem_atlas U := ⟨U, rfl⟩

set_option maxHeartbeats 500000 in
theorem realGrassmannian_standard_transition_contDiffOn {d : ℕ}
    (U W : RealGrassmannian V d) :
    ContDiffOn ℝ ⊤ ((realGrassmannianStandardChart U).symm.trans (realGrassmannianStandardChart W))
      ((realGrassmannianStandardChart U).symm.trans (realGrassmannianStandardChart W)).source := by
  intro A hA
  let cU := grassmannianModelCoordinate U
  let cW := grassmannianModelCoordinate W
  have hmem := hA.2.1
  simp only [OpenPartialHomeomorph.symm_symm] at hmem
  rw [realGrassmannianStandardChart_symm_apply] at hmem
  change IsUnit (graphCompression W.val
    (((realGrassmannianGraphChart U).symm (cU.symm A)).val.starProjection)) at hmem
  rw [realGrassmannianGraphChart_symm_projection] at hmem
  have hraw : ContDiffAt ℝ ⊤
      (fun B : U.val →L[ℝ] U.valᗮ => graphCoordinate W.val (subspaceGraphProjection U.val B))
      (cU.symm A) :=
    contDiffAt_rawGrassmannianGraphTransition (V := V) (d := d) U W (cU.symm A) hmem
  have hsecond : ContDiffAt ℝ ⊤
      (fun z => cW (graphCoordinate W.val (subspaceGraphProjection U.val (cU.symm z)))) A :=
    contDiffAt_linearCoordinates
      (E := U.val →L[ℝ] U.valᗮ) (F := W.val →L[ℝ] W.valᗮ)
      (G := GrassmannianModel V d) (H := GrassmannianModel V d)
      (n := ⊤) (f := fun B : U.val →L[ℝ] U.valᗮ =>
        graphCoordinate W.val (subspaceGraphProjection U.val B)) cU cW A hraw
  have hfun : (((realGrassmannianStandardChart U).symm.trans (realGrassmannianStandardChart W)) :
      GrassmannianModel V d → GrassmannianModel V d) =
      fun z => cW (graphCoordinate W.val (subspaceGraphProjection U.val (cU.symm z))) := by
    funext z
    rw [OpenPartialHomeomorph.trans_apply, realGrassmannianStandardChart_apply,
      realGrassmannianStandardChart_symm_apply]
    change cW (graphCoordinate W.val
      (((realGrassmannianGraphChart U).symm (cU.symm z)).val.starProjection)) = _
    rw [realGrassmannianGraphChart_symm_projection]
  rw [hfun]
  exact hsecond.contDiffWithinAt

theorem realGrassmannian_isManifold (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) :
    letI := realGrassmannianChartedSpace V d
    IsManifold (modelWithCornersSelf ℝ (GrassmannianModel V d)) ⊤ (RealGrassmannian V d) := by
  letI := realGrassmannianChartedSpace V d
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ (GrassmannianModel V d)) ⊤
  intro c e hc he
  change c ∈ range (realGrassmannianStandardChart (V := V) (d := d)) at hc
  change e ∈ range (realGrassmannianStandardChart (V := V) (d := d)) at he
  obtain ⟨U, rfl⟩ := hc
  obtain ⟨W, rfl⟩ := he
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ] using
    realGrassmannian_standard_transition_contDiffOn U W

end BanachIsometric
