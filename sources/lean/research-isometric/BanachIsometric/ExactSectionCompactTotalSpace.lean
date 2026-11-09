import BanachIsometric.ExactSectionComponentCovering
import BanachIsometric.CompactBundleTotalSpace

/-! The actual exact-section bundle over a compact parameter space is
compact, including its inherited parameter/operator topology. This supplies
the uniform neighborhood needed for finite-step homotopy lifting. -/

noncomputable section

namespace BanachIsometric.ExactSectionPrincipalData

open Set MeasureTheory
open scoped Topology NNReal

variable {P F : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : P → Submodule ℝ F} {a₀ : P}
    (D : BanachIsometric.ExactSectionPrincipalData m p H a₀)

theorem compactSpace_coreTotalSpace
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    CompactSpace D.core.TotalSpace := by
  obtain ⟨hS, _, h0⟩ := D.modelBody_geometric_properties hp hC
  letI : CompactSpace D.StructureGroup :=
    compactSpace_bodyAutomorphismGroup_of_interior μ D.ModelBody hS h0
  exact compactSpace_bundleCore_totalSpace D.core

theorem compactSpace_actualTotalSpace
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    CompactSpace (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) := by
  letI := D.compactSpace_coreTotalSpace μ hp hC
  exact D.totalSpaceHomeomorph.compactSpace

/-- Compactness of the literal set of all exact section operators in the
ambient parameter/operator product. -/
theorem isCompact_exactSectionOperators
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1)) :
    IsCompact {t : P × (EuclideanSpace ℝ (Fin m) →L[ℝ] F) |
      Function.Injective t.2 ∧ LinearMap.range t.2.toLinearMap = H t.1 ∧
        t.2 '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H t.1 : Set F)} :=
  isCompact_iff_compactSpace.mpr (D.compactSpace_actualTotalSpace μ hp hC)

end BanachIsometric.ExactSectionPrincipalData
