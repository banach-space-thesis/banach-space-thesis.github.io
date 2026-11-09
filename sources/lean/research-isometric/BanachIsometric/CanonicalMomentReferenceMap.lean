import BanachIsometric.CanonicalHemisphereOrientation
import BanachIsometric.RadialHomeomorphism

/-! The original radial gauge map in the oriented hemisphere coordinates. -/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Metric SingularPrism
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {p : F → ℝ}

def canonicalMomentReferenceMap (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v : sphere (0 : F) 1) (n : ℕ) (hdim : Module.finrank ℝ F = n + 3) :
    C(sphere (0 : F) 1, Fin (n + 3) → ℝ) :=
  ⟨fun u => canonicalHemisphereChartCoordinates v n hdim (radialGaugeMap p u.val),
    (canonicalHemisphereChartCoordinates v n hdim).continuous.comp
      ((radialGaugeHomeomorph hp hcont).continuous.comp continuous_subtype_val)⟩

end BanachIsometric.ExactSectionPrincipalData
