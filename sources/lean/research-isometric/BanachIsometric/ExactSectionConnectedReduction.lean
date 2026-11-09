import BanachIsometric.ExactSectionComponentCovering
import BanachIsometric.ConnectedReductionHomeomorph
import BanachIsometric.IdentityComponentProperties

/-! Connected compact structure-group reduction for the actual exact-section
bundle over the actual sphere, from the original gauge hypotheses. -/

noncomputable section

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology NNReal

/-- The first component-reduction part of Lemma 4.3, instantiated on the actual
exact-section principal bundle. The reduced core has the actual connected
identity subgroup as fiber and is homeomorphic over the base to the selected
component subbundle, with its inherited original-total-space topology.

No component-finiteness, covariance normalization, sphere simple connectivity
or component-cover section is assumed in this endpoint. -/
theorem ExactSectionPrincipalData.exists_sphere_connectedReduction
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (n : ℕ) (hn : 2 ≤ n) {m : ℕ} {p : F → ℝ}
    {H : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Submodule ℝ F}
    {a₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    ConnectedSpace (Subgroup.connectedComponentOfOne D.StructureGroup) ∧
    CompactSpace (Subgroup.connectedComponentOfOne D.StructureGroup) ∧
    ∃ s : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        D.atlas.componentCore.TotalSpace),
      (∀ a, D.atlas.componentCore.proj (s a) = a) ∧
      ∃ R : FiberBundleCore
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (Subgroup.connectedComponentOfOne D.StructureGroup),
        ∃ e : R.TotalSpace ≃ₜ D.atlas.SelectedComponent s,
          ∀ t, (e t).val.1 = t.1 := by
  obtain ⟨hS, _, h0⟩ := D.modelBody_geometric_properties hp hC
  letI : CompactSpace D.StructureGroup :=
    compactSpace_bodyAutomorphismGroup_of_interior μ D.ModelBody hS h0
  refine ⟨connectedSpace_connectedComponentOfOne _, compactSpace_connectedComponentOfOne _, ?_⟩
  obtain ⟨s, hs⟩ := D.exists_sphere_componentCovering_section n hn μ hp hC
  have hopen := D.isOpen_structureGroup_identityComponent μ hp hC
  exact ⟨s, hs, D.atlas.connectedReductionCore s hs hopen,
    D.atlas.connectedReductionHomeomorph s hs hopen, fun _ => rfl⟩

end BanachIsometric
