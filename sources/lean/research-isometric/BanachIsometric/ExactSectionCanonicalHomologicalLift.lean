import BanachIsometric.ExactSectionHomologicalLift
import BanachIsometric.CanonicalHemisphereCycle

/-! The topological lift can use the concrete normalized affine sphere cycle.
The homological condition is imposed on actual based clutching maps. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData
open Set Metric MeasureTheory SphereGenerator SingularPrism
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F} {a₀ : sphere (0 : F) 1}

theorem exists_canonical_homological_lift_of_zero_clutching_class
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1))
    (hProj : Continuous (fun a => (H a).starProjection))
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3)
    (hVanishing : ∀ g : C(EquatorSphere v, Subgroup.connectedComponentOfOne D.StructureGroup),
      g ((equatorStandardSphereHomeomorph v (n + 1) hdim).symm (sphereBasepoint (n + 1))) = 1 →
      rawHomologyMap g n (Submodule.Quotient.mk (canonicalEquatorCycle v n hdim)) = 0) :
    ∃ c : rawCycles (ExactSectionSpace D.ModelBody {y : F | p y ≤ 1} H) (n + 1),
      rawHomologyMap D.homologicalProjection (n + 1) (Submodule.Quotient.mk c) =
        Submodule.Quotient.mk (canonicalSuspensionCycle v n hdim) := by
  exact D.exists_homological_lift_of_zero_clutching_class μ hp hSphere hProj v n hdim
    (canonicalEquatorCycle v n hdim) (canonicalHemisphereChain v v n hdim)
    (canonicalHemisphereChain v (-v) n hdim) (canonicalNorthChain_boundary v n hdim)
    (canonicalSouthChain_boundary v n hdim) hVanishing

end BanachIsometric.ExactSectionPrincipalData
