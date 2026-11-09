import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.OpenPartialHomeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Changes of actual chart models by continuous linear equivalences preserve
analytic transitions, with their genuine partial-homeomorphism domains. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology

theorem contDiffOn_transition_postcompose_linearModels
    {X E F G : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : OpenPartialHomeomorph X E) (d : OpenPartialHomeomorph X F)
    (a : E ≃L[ℝ] G) (b : F ≃L[ℝ] G)
    (h : ContDiffOn ℝ ⊤ (c.symm.trans d) (c.symm.trans d).source) :
    ContDiffOn ℝ ⊤ ((c.trans a.toHomeomorph.toOpenPartialHomeomorph).symm.trans
      (d.trans b.toHomeomorph.toOpenPartialHomeomorph))
      ((c.trans a.toHomeomorph.toOpenPartialHomeomorph).symm.trans
        (d.trans b.toHomeomorph.toOpenPartialHomeomorph)).source := by
  intro z hz
  have hsource : a.symm z ∈ (c.symm.trans d).source := ⟨hz.1.2, hz.2.1⟩
  have hAt : ContDiffAt ℝ ⊤ (c.symm.trans d) (a.symm z) :=
    h.contDiffAt ((c.symm.trans d).open_source.mem_nhds hsource)
  have hfirst : ContDiffAt ℝ ⊤ (fun y => (c.symm.trans d) (a.symm y)) z :=
    hAt.comp z a.symm.contDiff.contDiffAt
  have hsecond : ContDiffAt ℝ ⊤ (fun y => b ((c.symm.trans d) (a.symm y))) z :=
    b.contDiff.contDiffAt.comp z hfirst
  exact hsecond.contDiffWithinAt

end BanachIsometric
