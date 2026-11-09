import BanachIsometric.ExactSectionLipschitzHomologicalLift
import BanachIsometric.SphericalPontryaginVanishing
import BanachIsometric.BodyIdentitySingularHomologyBound

/-! The actual identity component of the body group has bounded rational
homology. Consequently its based equatorial clutching maps kill the
positive even equator class, yielding the Lipschitz cycle lift. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData
open Set Metric MeasureTheory SphereGenerator SingularPrism
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_lipschitz_canonical_homological_lift_of_even_equator
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C L : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : LipschitzWith L (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (heven : Even (n + 1)) :
    ∃ d : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1),
      d.val ∈ rawLipschitzCarrier _ (n + 2) ∧
      ∃ b : RawRationalChains (sphere (0 : F) 1) (n + 3),
        b ∈ rawLipschitzCarrier _ (n + 3) ∧
        rawBoundary (n + 2) b = rawChainMap D.homologicalProjection (n + 2) d.val -
          (canonicalSuspensionCycle v n hdim).val := by
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hSphere
  obtain ⟨N, hN⟩ := bodyIdentityComponent_rawDegreeHomologyBounded μ D.ModelBody hS hreg h0
  apply D.exists_lipschitz_canonical_homological_lift μ hp hSphere hProj v n hdim
  intro g hg
  exact rawHomologyMap_even_sphere_image_zero N (fun q hq => hN.2 q (Nat.le_of_lt hq)) n
    (equatorStandardSphereHomeomorph v (n + 1) hdim) g hg n heven
    (canonicalEquatorCycle v n hdim)

end BanachIsometric.ExactSectionPrincipalData
