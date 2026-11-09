import BanachIsometric.GrassmannianGraphChart
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The local smooth-field criterion in the actual graph charts is equivalent
to smoothness of the actual projector field. Chart membership is established
on a neighborhood from compression invertibility; no continuity of the
subspace field is an extra premise. -/

noncomputable section
namespace BanachIsometric
open Set Filter
open scoped Topology Manifold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

def GrassmannianGraphSmoothAt {d : ℕ} (n : WithTop ℕ∞)
    (f : M → RealGrassmannian V d) (x : M) : Prop :=
  (∀ᶠ a in 𝓝 x, f a ∈ (realGrassmannianGraphChart (f x)).source) ∧
    ContMDiffAt I (modelWithCornersSelf ℝ ((f x).val →L[ℝ] (f x).valᗮ)) n
      (fun a => realGrassmannianGraphChart (f x) (f a)) x

theorem grassmannianGraphSmoothAt_iff_projection {d : ℕ} {n : WithTop ℕ∞}
    (f : M → RealGrassmannian V d) (x : M) :
    GrassmannianGraphSmoothAt I n f x ↔
      ContMDiffAt I (modelWithCornersSelf ℝ (V →L[ℝ] V)) n
        (fun a => (f a).val.starProjection) x := by
  constructor
  · rintro ⟨hmem, hcoord⟩
    have hp : ContMDiffAt I (modelWithCornersSelf ℝ (V →L[ℝ] V)) n
        (fun a => subspaceGraphProjection (f x).val (realGrassmannianGraphChart (f x) (f a))) x :=
      ((contDiff_subspaceGraphProjection (f x).val).of_le le_top).comp_contMDiffAt hcoord
    have heq : (fun a => (f a).val.starProjection) =ᶠ[𝓝 x]
        (fun a => subspaceGraphProjection (f x).val (realGrassmannianGraphChart (f x) (f a))) := by
      filter_upwards [hmem] with a ha
      have h := congrArg (fun U : RealGrassmannian V d => U.val.starProjection)
        ((realGrassmannianGraphChart (f x)).left_inv ha)
      dsimp only at h
      rw [realGrassmannianGraphChart_symm_projection] at h
      exact h.symm
    exact hp.congr_of_eventuallyEq heq
  · intro hp
    have hunit : IsUnit (graphCompression (f x).val (f x).val.starProjection) :=
      projectionGrassmannianGraphChart_center_mem (f x)
    have hc : ContinuousAt (fun a => graphCompression (f x).val (f a).val.starProjection) x :=
      (contDiff_graphCompression (f x).val).continuous.continuousAt.comp hp.continuousAt
    have hnear : ∀ᶠ a in 𝓝 x,
        IsUnit (graphCompression (f x).val (f a).val.starProjection) :=
      hc.preimage_mem_nhds ((Units.isOpen (R := (f x).val →L[ℝ] (f x).val)).mem_nhds hunit)
    refine ⟨hnear, ?_⟩
    have hraw : ContDiffAt ℝ n (graphCoordinate (f x).val) (f x).val.starProjection :=
      (contDiffAt_graphCoordinate (f x).val _ hunit).of_le le_top
    exact hraw.comp_contMDiffAt (I := I) (f := fun a : M => (f a).val.starProjection) (x := x) hp

end BanachIsometric
