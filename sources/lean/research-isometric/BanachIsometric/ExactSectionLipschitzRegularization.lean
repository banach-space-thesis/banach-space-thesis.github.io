import BanachIsometric.ExactSectionCorrectionRadius
import BanachIsometric.ExactSectionContinuousSections
import BanachIsometric.ProjectedCompactApproximation

/-!
# Lipschitz regularization of actual continuous exact sections

On a compact Euclidean parameter subset, approximate the genuine continuous
operator section, project it into the prescribed moving section subspaces,
and apply the actual equivariant body-group retraction in the constructed
finite atlas. The chart corrections agree exactly, and the finite open cover
upgrades their local Lipschitz bounds to a global one.

This is an alternative to a tubular-neighborhood regularization argument.
Neither a Lipschitz section nor an ambient retraction is assumed.
-/

namespace BanachIsometric

open Set MeasureTheory
open scoped NNReal

noncomputable section

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Actual operator-valued continuous exact sections on a compact Euclidean
parameter set admit global Lipschitz exact sections, in the original norms. -/
theorem exists_lipschitz_exact_section_of_continuous_on_compact {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    {s : Set P} (hs : IsCompact s)
    {S : Set (EuclideanSpace ℝ (Fin m))} {K : Set F} {H : s → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S)
    (A : C(s, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hA : ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
      A a '' S = K ∩ (H a : Set F)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection)) :
    ∃ B : s → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ L : ℝ≥0,
      LipschitzWith L B ∧ ∀ a, Function.Injective (B a) ∧
        LinearMap.range (B a).toLinearMap = H a ∧ B a '' S = K ∩ (H a : Set F) := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  letI : CompactSpace (bodyAutomorphismGroup S) :=
    compactSpace_bodyAutomorphismGroup_of_interior μ S hS h0
  obtain ⟨D⟩ := nonempty_ambientBodyRetraction μ S hS hreg h0
  obtain ⟨I, hcover⟩ := Z.exists_finset_chart_cover
  obtain ⟨δ, hδ, hDomain⟩ := Z.exists_uniform_correction_radius D A hA I
  have hRange : ∀ a : s, ∀ x, A a x ∈ H a := fun a x =>
    (hA a).2.1.le (LinearMap.mem_range_self (A a).toLinearMap x)
  obtain ⟨Y, LY, hYLip, hYRange, hYClose⟩ :=
    exists_projected_lipschitz_approximation_on_compact hs A H hProj hRange hδ
  exact Z.exists_lipschitz_exact_section_of_approximate D Y hYLip hYRange I hcover
    (hDomain Y hYClose)

namespace ExactSectionPrincipalData

variable {s : Set P} {m : ℕ} {p : F → ℝ} {H : s → Submodule ℝ F} {a₀ : s}
    (D : ExactSectionPrincipalData m p H a₀)

/-- The model-body geometry needed for regularization follows from the
original definite homogeneous gauge and its sphere Lipschitz estimate. -/
theorem exists_lipschitz_operator_section_of_continuous
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hs : IsCompact s) (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (A : C(s, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hA : ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H a ∧
      A a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H a : Set F)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection)) :
    ∃ B : s → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ L : ℝ≥0,
      LipschitzWith L B ∧ ∀ a, Function.Injective (B a) ∧
        LinearMap.range (B a).toLinearMap = H a ∧
        B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
  obtain ⟨Cp, hCp⟩ := hp.exists_lipschitzWith hSphere
  have hpR := hp.comp_linearIsometry D.reference
  have hLip : LipschitzWith Cp (fun x => p (D.reference x)) := by
    simpa only [mul_one] using hCp.comp D.reference.lipschitz
  have hS : IsCompact D.ModelBody := hpR.isCompact_sublevel hLip.lipschitzOnWith
  have hreg : closure (interior D.ModelBody) = D.ModelBody :=
    (hpR.sublevel_eq_closure_interior hLip.continuous).symm
  have h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior D.ModelBody :=
    hpR.zero_mem_interior_sublevel hLip.continuous.continuousOn
  exact exists_lipschitz_exact_section_of_continuous_on_compact μ hs D.atlas hS hreg h0
    A hA hProj

/-- A continuous section of the actual constructed Mathlib principal bundle
gives a genuine globally Lipschitz family of exact section operators. -/
theorem exists_lipschitz_operator_section_of_bundle_section
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hs : IsCompact s) (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (Metric.sphere (0 : F) 1))
    (σ : s → D.core.TotalSpace) (hσ : Continuous σ)
    (hbase : ∀ a, (σ a).proj = a) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection)) :
    ∃ B : s → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ L : ℝ≥0,
      LipschitzWith L B ∧ ∀ a, Function.Injective (B a) ∧
        LinearMap.range (B a).toLinearMap = H a ∧
        B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H a : Set F) := by
  obtain ⟨A, hA⟩ := D.atlas.exists_continuous_operator_section_of_bundle_section σ hσ hbase
  exact D.exists_lipschitz_operator_section_of_continuous μ hs hp hSphere A hA hProj

end ExactSectionPrincipalData

end
end BanachIsometric
