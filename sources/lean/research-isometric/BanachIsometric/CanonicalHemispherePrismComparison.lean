import BanachIsometric.CanonicalHemisphereCycle
import BanachIsometric.HemispherePrismChains

/-! The normalized affine cones and the direct prism fillings determine
the same actual singular homology class. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem canonicalSuspensionCycle_class_eq_prism (v : sphere (0 : V) 1) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) (heven : Even (n + 1)) :
    (Submodule.Quotient.mk (canonicalSuspensionCycle v n hdim) :
      RawPositiveHomology (sphere (0 : V) 1) (n + 1)) =
      Submodule.Quotient.mk (hemisphericalBaseCycle v n (canonicalEquatorCycle v n hdim)
        (rawHemispherePrismChain v (equatorNorth v) n (canonicalEquatorCycle v n hdim))
        (rawHemispherePrismChain (-v) (equatorSouth v) n (canonicalEquatorCycle v n hdim))
        (rawHemispherePrismChain_boundary v (equatorNorth v) n (canonicalEquatorCycle v n hdim) heven)
        (rawHemispherePrismChain_boundary (-v) (equatorSouth v) n (canonicalEquatorCycle v n hdim) heven)) :=
  hemisphericalBaseCycle_class_eq v n (canonicalEquatorCycle v n hdim) _ _ _ _
    (canonicalNorthChain_boundary v n hdim)
    (rawHemispherePrismChain_boundary v (equatorNorth v) n (canonicalEquatorCycle v n hdim) heven)
    (canonicalSouthChain_boundary v n hdim)
    (rawHemispherePrismChain_boundary (-v) (equatorSouth v) n (canonicalEquatorCycle v n hdim) heven)

end BanachIsometric.SingularPrism
