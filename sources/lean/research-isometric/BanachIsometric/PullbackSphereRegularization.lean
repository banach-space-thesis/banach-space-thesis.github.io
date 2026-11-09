import BanachIsometric.ExactSectionAtlasPullback
import BanachIsometric.ExactSectionEndpointTransport
import BanachIsometric.ExactSectionLipschitzRegularization
import BanachIsometric.CloseSphereHomotopy

/-! An actual continuous sphere pullback having an exact section can be
replaced by a homotopic Lipschitz sphere map having a Lipschitz exact operator
section. The base homotopy is transported by the proved finite-step geometric
retraction construction; no invariance of bundle classification is assumed.
The base map and the exact operator family are both regularized explicitly. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData
open Set Metric MeasureTheory
open scoped Topology NNReal

theorem exists_lipschitz_sphere_pullback_section_of_continuous
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : V) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (A : C(sphere (0 : V) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hA : ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H (φ a) ∧
      A a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (φ a) : Set F)) :
    ∃ ψ : C(sphere (0 : V) 1, sphere (0 : V) 1), ∃ Lψ : ℝ≥0,
    ∃ B : sphere (0 : V) 1 → EuclideanSpace ℝ (Fin m) →L[ℝ] F, ∃ LB : ℝ≥0,
      LipschitzWith Lψ ψ ∧ LipschitzWith LB B ∧
      Nonempty (ContinuousMap.Homotopy φ ψ) ∧
      ∀ a, Function.Injective (B a) ∧ LinearMap.range (B a).toLinearMap = H (ψ a) ∧
        B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (ψ a) : Set F) := by
  letI : CompactSpace (sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  obtain ⟨ψ, Lψ, hψ, _, ⟨hom⟩⟩ := exists_lipschitz_sphere_map_homotopic φ
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hseed : ∀ a, Function.Injective (A a) ∧
      LinearMap.range (A a).toLinearMap = H (hom (0, a)) ∧
      A a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (hom (0, a)) : Set F) := by
    intro a
    rw [hom.apply_zero]
    exact hA a
  obtain ⟨A₁, hA₁, _⟩ := D.exists_continuous_endpoint_section μ hp hC hProj.continuous
    hom.toContinuousMap A hseed
  have hvalid : ∀ a, Function.Injective (A₁ a) ∧
      LinearMap.range (A₁ a).toLinearMap = H (ψ a) ∧
      A₁ a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (ψ a) : Set F) := by
    intro a
    have ha := hA₁ a
    change Function.Injective (A₁ a) ∧
      LinearMap.range (A₁ a).toLinearMap = H (hom (1, a)) ∧
      A₁ a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (hom (1, a)) : Set F) at ha
    simpa only [hom.apply_one] using ha
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hC
  obtain ⟨B, LB, hB, hBvalid⟩ := exists_lipschitz_exact_section_of_continuous_on_compact
    μ (isCompact_sphere (0 : V) 1) (D.atlas.pullback ψ hψ) hS hreg h0 A₁ hvalid (hProj.comp hψ)
  exact ⟨ψ, Lψ, B, LB, hψ, hB, ⟨hom⟩, hBvalid⟩

end BanachIsometric.ExactSectionPrincipalData
