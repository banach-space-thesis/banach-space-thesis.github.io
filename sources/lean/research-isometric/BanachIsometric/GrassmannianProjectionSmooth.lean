import BanachIsometric.GrassmannianManifold
import BanachIsometric.GrassmannianGraphFields
import BanachIsometric.AnalyticCoordinateComposition
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Actual graph-chart Grassmannian smoothness is equivalent to smoothness of
its canonical orthogonal-projection field. This is a proved chart calculation,
not a definition of smooth Grassmannian maps by projector smoothness. The
Grassmannian has its explicit d(dim V-d)-dimensional Euclidean model. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology Manifold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem continuous_realGrassmannianProjector {d : ℕ} :
    Continuous (fun U : RealGrassmannian V d => U.val.starProjection) :=
  continuous_subtype_val.comp (realGrassmannianProjectionIsometry V d).isometry.continuous

section Fields
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

set_option maxHeartbeats 500000 in
theorem contMDiff_realGrassmannian_iff_projection {d : ℕ}
    {n : WithTop ℕ∞} (f : M → RealGrassmannian V d) :
    letI := realGrassmannianChartedSpace V d
    ContMDiff I (modelWithCornersSelf ℝ (GrassmannianModel V d)) n f ↔
      ContMDiff I (modelWithCornersSelf ℝ (V →L[ℝ] V)) n
        (fun a => (f a).val.starProjection) := by
  letI := realGrassmannianChartedSpace V d
  letI := realGrassmannian_isManifold V d
  constructor
  · intro hf
    intro x
    apply (grassmannianGraphSmoothAt_iff_projection I f x).mp
    have hmem : ∀ᶠ a in 𝓝 x, f a ∈ (realGrassmannianGraphChart (f x)).source :=
      (hf x).continuousAt.preimage_mem_nhds
        ((realGrassmannianGraphChart (f x)).open_source.mem_nhds
          (realGrassmannianGraphChart_center_mem (f x)))
    refine ⟨hmem, ?_⟩
    let c : ((f x).val →L[ℝ] (f x).valᗮ) ≃L[ℝ] GrassmannianModel V d :=
      grassmannianModelCoordinate (f x)
    have hchart := ((contMDiffAt_iff_target_of_mem_source
      (mem_chart_source (GrassmannianModel V d) (f x))).mp (hf x)).2
    change ContMDiffAt I (modelWithCornersSelf ℝ (GrassmannianModel V d)) n
      (fun a => c (realGrassmannianGraphChart (f x) (f a))) x at hchart
    have hback := contMDiffAt_postcomp_linearEquiv
      (E := GrassmannianModel V d) (F := (f x).val →L[ℝ] (f x).valᗮ) I
      (fun a => c (realGrassmannianGraphChart (f x) (f a))) c.symm x hchart
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hback
  · intro hp
    let p : M → ProjectionGrassmannian V d := fun a => realGrassmannianProjection V d (f a)
    have hpc : Continuous p := hp.continuous.subtype_mk _
    have hfcont : Continuous f := by
      have h := (realGrassmannianProjectionIsometry V d).symm.isometry.continuous.comp hpc
      have heq : f = (realGrassmannianProjectionIsometry V d).symm ∘ p := by
        funext a
        exact ((realGrassmannianProjectionIsometry V d).symm_apply_apply (f a)).symm
      rw [heq]
      exact h
    intro x
    apply (contMDiffAt_iff_target_of_mem_source
      (mem_chart_source (GrassmannianModel V d) (f x))).mpr
    refine ⟨hfcont.continuousAt, ?_⟩
    have hCoord := ((grassmannianGraphSmoothAt_iff_projection I f x).mpr (hp x)).2
    let c : ((f x).val →L[ℝ] (f x).valᗮ) ≃L[ℝ] GrassmannianModel V d :=
      grassmannianModelCoordinate (f x)
    change ContMDiffAt I (modelWithCornersSelf ℝ (GrassmannianModel V d)) n
      (fun a => c (realGrassmannianGraphChart (f x) (f a))) x
    exact contMDiffAt_postcomp_linearEquiv I
      (fun a : M => realGrassmannianGraphChart (f x) (f a)) c x hCoord

end Fields

theorem contMDiff_realGrassmannianProjector (d : ℕ) :
    letI := realGrassmannianChartedSpace V d
    ContMDiff (modelWithCornersSelf ℝ (GrassmannianModel V d))
      (modelWithCornersSelf ℝ (V →L[ℝ] V)) ⊤
      (fun U : RealGrassmannian V d => U.val.starProjection) := by
  letI := realGrassmannianChartedSpace V d
  exact (contMDiff_realGrassmannian_iff_projection
    (I := modelWithCornersSelf ℝ (GrassmannianModel V d)) (n := ⊤)
    (id : RealGrassmannian V d → RealGrassmannian V d)).mp contMDiff_id

end BanachIsometric
