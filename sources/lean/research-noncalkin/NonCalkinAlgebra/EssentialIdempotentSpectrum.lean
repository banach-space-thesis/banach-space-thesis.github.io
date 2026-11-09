import NonCalkinAlgebra.CompactSpectralFiniteness
import NonCalkinAlgebra.SpectralLiftingPreliminaries

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

/-- The spectral-countability step in Lemma 2.4, now with the compact
spectral theorem proved rather than retained as a premise. -/
theorem essential_idempotent_spectrum_countable (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) : (spectrum ℂ T).Countable :=
  spectrum_countable_of_defect_spectrum_countable T
    (compact_spectrum_countable (T * T - T) (operatorIdeal_le_compact X convention hT))

/-- A positively oriented circle of some radius in (0,1) can be used for
the Riesz integral: its entire boundary is in the actual operator resolvent. -/
theorem essential_idempotent_resolvent_circle (T : BoundedOperators X)
    (hT : T * T - T ∈ operatorIdeal X convention) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T := by
  obtain ⟨r, hr0, hr1, hr⟩ := exists_circle_missing_countable_set
    (essential_idempotent_spectrum_countable X convention T hT)
  refine ⟨r, hr0, hr1, ?_⟩
  intro z hz
  have hn : z ∉ spectrum ℂ T := fun hmem => hr z hmem hz
  exact spectrum.notMem_iff.mp hn

end NonCalkinAlgebra
