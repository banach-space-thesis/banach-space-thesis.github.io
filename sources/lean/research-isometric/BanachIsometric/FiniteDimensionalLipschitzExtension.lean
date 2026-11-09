import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz

/-! A Lipschitz map on a subtype extends into a finite-dimensional real
normed space by extending its finitely many coordinates. -/

noncomputable section
namespace BanachIsometric

open Set
open scoped NNReal

theorem exists_lipschitz_extension_finiteDimensional {X W : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (s : Set X) (f : s → W) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃ F : X → W, (∃ K : ℝ≥0, LipschitzWith K F) ∧ ∀ x : s, F x.val = f x := by
  classical
  let e := (Module.finBasis ℝ W).equivFun.toContinuousLinearEquiv
  let g : X → (Fin (Module.finrank ℝ W) → ℝ) := fun x => if hx : x ∈ s then e (f ⟨x, hx⟩) else 0
  have he : s.restrict g = e ∘ f := by
    funext x
    simp only [Set.restrict_apply, g, dif_pos x.property, Function.comp_apply]
  have hg : LipschitzOnWith (‖e.toContinuousLinearMap‖₊ * L) g s := by
    rw [lipschitzOnWith_iff_restrict, he]
    exact e.lipschitz.comp hf
  obtain ⟨G, hG, hEq⟩ := hg.extend_pi
  refine ⟨e.symm ∘ G, ⟨_, e.symm.lipschitz.comp hG⟩, ?_⟩
  intro x
  have hx := (hEq x.property).symm
  simp only [g, dif_pos x.property] at hx
  change e.symm (G x.val) = f x
  rw [hx, e.symm_apply_apply]

end BanachIsometric
