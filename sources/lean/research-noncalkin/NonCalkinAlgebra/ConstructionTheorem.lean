import NonCalkinAlgebra.CornerModel
import NonCalkinAlgebra.MatrixDensity

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
variable (D : Type) [NormedRing D] [NormedAlgebra ℂ D]
  [NormOneClass D] [Nontrivial D] [CompleteSpace D]

/-- The density and ideal-lattice conclusions of the paper's construction,
for a coefficient algebra with the stated properties. This is not the
unconditional non-Calkin existence theorem. -/
theorem matrixBanachAlgebra_density_and_ideal_structure
    (hDdensity : HasDensityCharacter D Cardinal.continuum)
    (hDsimple : IsTopologicallySimple D) :
    HasDensityCharacter (matrixBanachAlgebra D).Carrier Cardinal.continuum ∧
      HasExactlyOneNonzeroProperClosedIdeal (matrixBanachAlgebra D).Carrier :=
  ⟨matrixAlgebra_density_continuum D hDdensity,
    matrixAlgebra_has_exactly_one_ideal D hDsimple⟩

end NonCalkinAlgebra
