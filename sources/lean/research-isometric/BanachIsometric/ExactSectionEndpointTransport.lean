import BanachIsometric.CompactFiberwiseTransport
import BanachIsometric.ExactSectionCompactTotalSpace
import BanachIsometric.ExactSectionGeometricRetraction

/-! Finite-step endpoint transport for the actual exact-section operators.
All compactness and neighborhood-retraction inputs are derived from the
original geometry rather than assumed in this endpoint. -/

noncomputable section

namespace BanachIsometric.ExactSectionPrincipalData

open Set MeasureTheory
open scoped Topology NNReal unitInterval

variable {P F A : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [PseudoMetricSpace A] [CompactSpace A]
    {m : ℕ} {p : F → ℝ} {H : P → Submodule ℝ F} {a₀ : P}
    (D : BanachIsometric.ExactSectionPrincipalData m p H a₀)

theorem exists_continuous_endpoint_section
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (f : C(I × A, P)) (seed : C(A, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hseed : ∀ a, Function.Injective (seed a) ∧
      LinearMap.range (seed a).toLinearMap = H (f (0, a)) ∧
      seed a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (f (0, a)) : Set F)) :
    ∃ out : C(A, EuclideanSpace ℝ (Fin m) →L[ℝ] F),
      (∀ a, Function.Injective (out a) ∧ LinearMap.range (out a).toLinearMap = H (f (1, a)) ∧
        out a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (f (1, a)) : Set F)) ∧
      ∀ a, (∀ t : I, f (t, a) = f (0, a)) → out a = seed a := by
  let K : Set (P × (EuclideanSpace ℝ (Fin m) →L[ℝ] F)) :=
    {t | Function.Injective t.2 ∧ LinearMap.range t.2.toLinearMap = H t.1 ∧
      t.2 '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H t.1 : Set F)}
  have hK : IsCompact K := D.isCompact_exactSectionOperators μ hp hC
  obtain ⟨U, r, hU, hr, hinside, hvalid, hfix⟩ :=
    D.exists_continuous_fiberwise_neighborhood_retraction μ hp hC hProj
  exact exists_continuous_endpoint_transport hK hU
    (fun t ht => hinside ⟨t, ht⟩) r hr hvalid
    (fun t ht => hfix ⟨t, ht⟩) f seed hseed

end BanachIsometric.ExactSectionPrincipalData
