import BanachIsometric.ComponentBundleReduction
import BanachIsometric.BodyGroupConjugation

/-!
# The finite component covering from the original geometric hypotheses

The reference body's compactness, regular closedness and interior origin are
derived from the original homogeneous gauge and its sphere regularity.
Covariance normalization, component openness and the actual covering are
therefore conclusions. On actual spheres of dimension at least two, a
continuous section of the actual associated covering is constructed.
-/

noncomputable section

namespace BanachIsometric

open Set MeasureTheory
open scoped Topology NNReal

namespace ExactSectionPrincipalData

variable {P F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : P → Submodule ℝ F} {a₀ : P}
    (D : ExactSectionPrincipalData m p H a₀)

theorem modelBody_geometric_properties
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    IsCompact D.ModelBody ∧ closure (interior D.ModelBody) = D.ModelBody ∧
      (0 : EuclideanSpace ℝ (Fin m)) ∈ interior D.ModelBody := by
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hC
  have hq := hp.comp_linearIsometry D.reference
  have hLip := hL.comp D.reference.lipschitz
  exact ⟨hq.isCompact_sublevel hLip.lipschitzOnWith,
    (hq.sublevel_eq_closure_interior hLip.continuous).symm,
    hq.zero_mem_interior_sublevel hLip.continuous.continuousOn⟩

theorem isOpen_structureGroup_identityComponent
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    IsOpen (Subgroup.connectedComponentOfOne D.StructureGroup : Set D.StructureGroup) := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hC
  exact isOpen_bodyAutomorphismGroup_connectedComponent_of_interior μ D.ModelBody hS hreg h0

theorem finite_structureGroup_components
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    Finite (D.StructureGroup ⧸ Subgroup.connectedComponentOfOne D.StructureGroup) := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hC
  exact finite_bodyAutomorphismGroup_componentQuotient_of_interior μ D.ModelBody hS hreg h0

theorem isCoveringMap_componentProjection
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    IsCoveringMap D.atlas.componentCore.proj :=
  D.atlas.isCoveringMap_componentCore (D.isOpen_structureGroup_identityComponent μ hp hC)

end ExactSectionPrincipalData

/-- The actual associated component covering of the constructed exact-section
bundle on an actual Euclidean sphere has a continuous section. -/
theorem ExactSectionPrincipalData.exists_sphere_componentCovering_section
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (n : ℕ) (hn : 2 ≤ n) {m : ℕ} {p : F → ℝ}
    {H : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → Submodule ℝ F}
    {a₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    ∃ s : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      D.atlas.componentCore.TotalSpace), ∀ a, D.atlas.componentCore.proj (s a) = a := by
  letI := simplyConnectedSpace_euclidean_sphere n hn
  letI := locPathConnectedSpace_euclidean_sphere n
  exact D.atlas.exists_componentCore_section (D.isOpen_structureGroup_identityComponent μ hp hC) a₀

end BanachIsometric
