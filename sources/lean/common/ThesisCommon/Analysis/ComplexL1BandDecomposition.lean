import ThesisCommon.Analysis.ComplexL1BandProjection
import ThesisCommon.Analysis.ComplexL1ModulusArithmetic

/-! Modulus identities for the complex band projection and its complement. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {I : Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)}

theorem complexL1BandProjection_residual_modulus (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (T-complexL1BandProjection hI T) =
      complexL1OperatorModulus T - bandProjection hI (complexL1OperatorModulus T) := by
  apply le_antisymm
  · apply (complexL1OperatorModulus_phase_isLUB _).2
    rintro _ ⟨c,hc,rfl⟩
    rw [complexL1OperatorPhase_sub,complexL1BandProjection_apply,
      complexL1OperatorPhase_bandProjectionFn]
    exact positive_operator_monotone
      (show 0 ≤ ContinuousLinearMap.id ℝ _ - bandProjection hI from sub_nonneg.mpr hI.bandProjection_le_id)
      ((complexL1OperatorModulus_phase_isLUB T).1 ⟨c,hc,rfl⟩)
  · have h := complexL1OperatorModulus_add_le (T-complexL1BandProjection hI T) (complexL1BandProjection hI T)
    rw [sub_add_cancel,complexL1BandProjection_modulus] at h
    exact sub_le_iff_le_add.mpr h

theorem complexL1BandProjection_modulus_decomposition (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus T =
      complexL1OperatorModulus (T-complexL1BandProjection hI T) +
        complexL1OperatorModulus (complexL1BandProjection hI T) := by
  rw [complexL1BandProjection_residual_modulus,complexL1BandProjection_modulus,sub_add_cancel]

theorem complexL1BandProjection_norm_decomposition (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖T‖ = ‖complexL1OperatorModulus (T-complexL1BandProjection hI T) +
      complexL1OperatorModulus (complexL1BandProjection hI T)‖ := by
  rw [← complexL1BandProjection_modulus_decomposition,norm_complexL1OperatorModulus]

theorem complexL1BandProjection_eq_zero_iff_modulus (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI T = 0 ↔ bandProjection hI (complexL1OperatorModulus T) = 0 := by
  rw [← complexL1BandProjection_modulus]
  constructor
  · intro h
    rw [h,complexL1OperatorModulus_zero]
  · intro h
    apply norm_eq_zero.mp
    rw [← norm_complexL1OperatorModulus,h,norm_zero]

theorem complexL1BandProjection_eq_self_iff_modulus_mem (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI T = T ↔ complexL1OperatorModulus T ∈ I := by
  constructor
  · intro h
    rw [← h,complexL1BandProjection_modulus]
    exact hI.bandProjection_mem _
  · intro h
    have hz : T-complexL1BandProjection hI T = 0 := by
      apply norm_eq_zero.mp
      rw [← norm_complexL1OperatorModulus,complexL1BandProjection_residual_modulus,
        hI.bandProjection_eq_self h,sub_self,norm_zero]
    exact (sub_eq_zero.mp hz).symm

theorem complexL1BandProjection_residual_disjoint (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) {R : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hR : R ∈ I) :
    complexL1OperatorModulus (T-complexL1BandProjection hI T) ⊓ |R| = 0 := by
  rw [complexL1BandProjection_residual_modulus]
  have hp : 0 ≤ complexL1OperatorModulus T - bandProjection hI (complexL1OperatorModulus T) :=
    sub_nonneg.mpr (hI.bandProjection_le_id _ (complexL1OperatorModulus_nonneg T))
  simpa only [abs_of_nonneg hp] using hI.residual_disjoint (complexL1OperatorModulus T) hR

end ThesisCommon
