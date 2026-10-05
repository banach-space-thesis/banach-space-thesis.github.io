import ThesisCommon.Analysis.ComplexL1BandDecomposition
import ThesisCommon.Analysis.SigmaComplexLatticeModulus

/-! A complex operator belongs to a complexified real band exactly when
its real and imaginary components do, equivalently when its modulus does. -/
noncomputable section
open MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {I : Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)}

theorem abs_complexL1OperatorRe_le_modulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    |complexL1OperatorRe T| ≤ complexL1OperatorModulus T := by
  apply sup_le
  · simpa [complexL1OperatorPhase] using
      (complexL1OperatorModulus_phase_isLUB T).1 ⟨1,by simp,rfl⟩
  · simpa [complexL1OperatorPhase] using
      (complexL1OperatorModulus_phase_isLUB T).1 ⟨-1,by simp,rfl⟩

theorem abs_complexL1OperatorIm_le_modulus (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    |complexL1OperatorIm T| ≤ complexL1OperatorModulus T := by
  apply sup_le
  · simpa [complexL1OperatorPhase] using
      (complexL1OperatorModulus_phase_isLUB T).1 ⟨-Complex.I,by simp,rfl⟩
  · simpa [complexL1OperatorPhase] using
      (complexL1OperatorModulus_phase_isLUB T).1 ⟨Complex.I,by simp,rfl⟩

theorem complexL1OperatorModulus_le_abs_re_add_abs_im (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus T ≤ |complexL1OperatorRe T| + |complexL1OperatorIm T| := by
  apply (complexL1OperatorModulus_phase_isLUB T).2
  rintro _ ⟨c,hc,rfl⟩
  exact complexLatticePhase_le_abs_add _ _ c hc.le

theorem complexL1OperatorModulus_mem_iff (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus T ∈ I ↔ complexL1OperatorRe T ∈ I ∧ complexL1OperatorIm T ∈ I := by
  constructor
  · intro h
    constructor
    · apply hI.solid h
      rw [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus T from complexL1OperatorModulus_nonneg T)]
      exact abs_complexL1OperatorRe_le_modulus T
    · apply hI.solid h
      rw [abs_of_nonneg (show 0 ≤ complexL1OperatorModulus T from complexL1OperatorModulus_nonneg T)]
      exact abs_complexL1OperatorIm_le_modulus T
  · rintro ⟨hr,hi⟩
    exact hI.nonneg_le_mem (I.add_mem (hI.abs_mem hr) (hI.abs_mem hi))
      (complexL1OperatorModulus_nonneg T) (complexL1OperatorModulus_le_abs_re_add_abs_im T)

theorem complexL1BandProjection_eq_self_iff_components (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI T = T ↔ complexL1OperatorRe T ∈ I ∧ complexL1OperatorIm T ∈ I := by
  rw [complexL1BandProjection_eq_self_iff_modulus_mem,complexL1OperatorModulus_mem_iff hI]

end ThesisCommon
