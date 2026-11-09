import NonCalkinAlgebra.MetricCardinality

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra

/-- At continuum density a metric space has exactly continuum many points.
This permits the discrete, rather than metric-density, counting of order
invariants for the coefficient algebras. It does not prove abundance. -/
theorem cardinal_eq_continuum_of_density_continuum {E : Type} [MetricSpace E]
    (hE : HasDensityCharacter E Cardinal.continuum) :
    Cardinal.mk E = Cardinal.continuum := by
  apply le_antisymm (cardinal_le_continuum_of_density_continuum hE)
  simpa only [Cardinal.mk_univ] using hE.2 Set.univ dense_univ

end NonCalkinAlgebra
