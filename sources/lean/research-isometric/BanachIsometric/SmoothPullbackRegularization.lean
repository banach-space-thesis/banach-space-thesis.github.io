import BanachIsometric.SmoothSphereApproximation
import BanachIsometric.PullbackSphereRegularization

/-!
# Smooth pullback maps and actual Lipschitz exact sections

The supplied continuous pullback map and its exact section are replaced by a
smooth, homotopic sphere map carrying a globally Lipschitz exact operator
section. Transport follows the actual homotopy using the proved geometric
fiberwise retraction. No bundle-classification homotopy principle is assumed.
-/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology NNReal Manifold

theorem exists_smooth_sphere_pullback_lipschitz_section
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    {m : ℕ} {p : F → ℝ} {H : sphere (0 : V) 1 → Submodule ℝ F}
    {a₀ : sphere (0 : V) 1} (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (A : C(sphere (0 : V) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hA : ∀ a, Function.Injective (A a) ∧ LinearMap.range (A a).toLinearMap = H (φ a) ∧
      A a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (φ a) : Set F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : C(sphere (0 : V) 1, sphere (0 : V) 1),
      ContMDiff (𝓡 n) (𝓡 n) (⊤ : ℕ∞) ψ ∧ ∃ Lψ : ℝ≥0,
      LipschitzWith Lψ ψ ∧ (∀ z, dist (ψ z) (φ z) < ε) ∧
      Nonempty (ContinuousMap.Homotopy φ ψ) ∧
      ∃ B : C(sphere (0 : V) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F), ∃ LB : ℝ≥0,
        LipschitzWith LB B ∧ ∀ a, Function.Injective (B a) ∧
          LinearMap.range (B a).toLinearMap = H (ψ a) ∧
          B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (ψ a) : Set F) := by
  letI : CompactSpace (sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  obtain ⟨ψ, hsmooth, Lψ, hψ, hclose, ⟨hom⟩⟩ :=
    exists_smooth_lipschitz_sphere_map_homotopic (n := n) φ hε
  have hseed : ∀ a, Function.Injective (A a) ∧
      LinearMap.range (A a).toLinearMap = H (hom (0, a)) ∧
      A a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (hom (0, a)) : Set F) := by
    intro a
    rw [hom.apply_zero]
    exact hA a
  obtain ⟨A₁, hA₁, _hfixed⟩ := D.exists_continuous_endpoint_section
    μ hp hSphere hProj.continuous hom.toContinuousMap A hseed
  have hvalid : ∀ a, Function.Injective (A₁ a) ∧
      LinearMap.range (A₁ a).toLinearMap = H (ψ a) ∧
      A₁ a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (ψ a) : Set F) := by
    intro a
    have ha := hA₁ a
    change Function.Injective (A₁ a) ∧
      LinearMap.range (A₁ a).toLinearMap = H (hom (1, a)) ∧
      A₁ a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (hom (1, a)) : Set F) at ha
    simpa only [hom.apply_one] using ha
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hSphere
  obtain ⟨B, LB, hB, hBvalid⟩ := exists_lipschitz_exact_section_of_continuous_on_compact
    μ (isCompact_sphere (0 : V) 1) (D.atlas.pullback ψ hψ) hS hreg h0 A₁ hvalid (hProj.comp hψ)
  exact ⟨ψ, hsmooth, Lψ, hψ, hclose, ⟨hom⟩, ⟨B, hB.continuous⟩, LB, hB, hBvalid⟩

end BanachIsometric.ExactSectionPrincipalData
