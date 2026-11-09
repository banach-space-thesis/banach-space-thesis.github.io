import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Explicit continuous linear coordinate changes preserve smoothness. -/

namespace BanachIsometric
open scoped Manifold

theorem contDiff_precomp_linearEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} (f : E → F) (a : E ≃L[ℝ] G) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun y : G => f (a.symm y)) :=
  ContDiff.comp (f := fun y : G => a.symm y) (g := f) hf a.symm.contDiff

theorem contMDiffAt_postcomp_linearEquiv
    {E F G H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ G H) {n : WithTop ℕ∞}
    (f : M → E) (a : E ≃L[ℝ] F) (x : M)
    (hf : ContMDiffAt I (modelWithCornersSelf ℝ E) n f x) :
    ContMDiffAt I (modelWithCornersSelf ℝ F) n (fun y => a (f y)) x :=
  a.contDiff.contDiffAt.comp_contMDiffAt (I := I) (f := f) (x := x) hf

end BanachIsometric
