import BanachIsometric.ExactSectionNeighborhood
import BanachIsometric.ExactSectionComponentCovering

/-! The actual neighborhood retraction for the geometrically constructed
principal bundle, with the body-group retraction constructed internally. -/

namespace BanachIsometric.ExactSectionPrincipalData

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {P F : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : P → Submodule ℝ F} {a₀ : P}
    (D : BanachIsometric.ExactSectionPrincipalData m p H a₀)

theorem exists_continuous_fiberwise_neighborhood_retraction
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection)) :
    ∃ U : Set (P × (EuclideanSpace ℝ (Fin m) →L[ℝ] F)),
      ∃ r : (P × (EuclideanSpace ℝ (Fin m) →L[ℝ] F)) → (EuclideanSpace ℝ (Fin m) →L[ℝ] F),
      IsOpen U ∧ ContinuousOn r U ∧
      (∀ t : ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H, t.val ∈ U) ∧
      (∀ t ∈ U, Function.Injective (r t) ∧ LinearMap.range (r t).toLinearMap = H t.1 ∧
        r t '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H t.1 : Set F)) ∧
      ∀ t : ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H, r t.val = t.val.2 := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hC
  obtain ⟨R⟩ := nonempty_ambientBodyRetraction μ D.ModelBody hS hreg h0
  exact D.atlas.exists_continuous_fiberwise_neighborhood_retraction R hProj

end
end BanachIsometric.ExactSectionPrincipalData
