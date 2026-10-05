import ThesisCommon.Analysis.ComplexL1OperatorPhases
import ThesisCommon.Analysis.BandProjectionSuprema

/-! A real operator-band projection induces an actual contractive complex
operator projection and commutes with the constructed complex modulus. -/
noncomputable section
open MeasureTheory Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {I : Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)}

def complexL1BandProjectionFn (hI : IsOrderClosedIdeal I) (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν :=
  complexL1Extension (bandProjection hI (complexL1OperatorRe T)) +
    Complex.I • complexL1Extension (bandProjection hI (complexL1OperatorIm T))

@[simp] theorem complexL1OperatorRe_bandProjectionFn (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorRe (complexL1BandProjectionFn hI T) = bandProjection hI (complexL1OperatorRe T) := by
  simp [complexL1BandProjectionFn,complexL1OperatorRe_smul]

@[simp] theorem complexL1OperatorIm_bandProjectionFn (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorIm (complexL1BandProjectionFn hI T) = bandProjection hI (complexL1OperatorIm T) := by
  simp [complexL1BandProjectionFn,complexL1OperatorIm_smul]

theorem complexL1OperatorPhase_bandProjectionFn (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (c : ℂ) :
    complexL1OperatorPhase (complexL1BandProjectionFn hI T) c =
      bandProjection hI (complexL1OperatorPhase T c) := by
  simp [complexL1OperatorPhase]

theorem complexL1OperatorModulus_bandProjectionFn (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (complexL1BandProjectionFn hI T) =
      bandProjection hI (complexL1OperatorModulus T) := by
  have hs : {A | ∃ c : ℂ, ‖c‖=1 ∧ A=complexL1OperatorPhase T c}.Nonempty :=
    ⟨complexL1OperatorPhase T 1,1,by simp,rfl⟩
  have h := hI.bandProjection_isLUB hs (complexL1OperatorModulus_phase_isLUB T)
  have he : bandProjection hI '' {A | ∃ c : ℂ, ‖c‖=1 ∧ A=complexL1OperatorPhase T c} =
      {A | ∃ c : ℂ, ‖c‖=1 ∧ A=complexL1OperatorPhase (complexL1BandProjectionFn hI T) c} := by
    ext A
    constructor
    · rintro ⟨B,⟨c,hc,rfl⟩,rfl⟩
      exact ⟨c,hc,(complexL1OperatorPhase_bandProjectionFn hI T c).symm⟩
    · rintro ⟨c,hc,rfl⟩
      exact ⟨complexL1OperatorPhase T c,⟨c,hc,rfl⟩,complexL1OperatorPhase_bandProjectionFn hI T c |>.symm⟩
  rw [he] at h
  exact (complexL1OperatorModulus_phase_isLUB _).unique h

theorem norm_complexL1BandProjectionFn_le (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) : ‖complexL1BandProjectionFn hI T‖ ≤ ‖T‖ := by
  rw [← norm_complexL1OperatorModulus,complexL1OperatorModulus_bandProjectionFn,
    ← norm_complexL1OperatorModulus T]
  exact norm_le_norm_of_abs_le_abs (hI.abs_bandProjection_le _)

/-- The genuine complex-linear contractive projection on the operator space. -/
def complexL1BandProjection (hI : IsOrderClosedIdeal I) :
    (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) →L[ℂ] (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :=
  LinearMap.mkContinuous
    { toFun := complexL1BandProjectionFn hI
      map_add' := by
        intro T U
        apply complexL1Operator_ext <;> simp
      map_smul' := by
        intro c T
        apply complexL1Operator_ext
        · simp [complexL1OperatorRe_smul]
        · simp [complexL1OperatorIm_smul] }
    1 (by intro T; simpa only [one_mul] using norm_complexL1BandProjectionFn_le hI T)

theorem complexL1BandProjection_apply (hI : IsOrderClosedIdeal I) (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI T = complexL1BandProjectionFn hI T := rfl

theorem complexL1BandProjection_modulus (hI : IsOrderClosedIdeal I) (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1OperatorModulus (complexL1BandProjection hI T) = bandProjection hI (complexL1OperatorModulus T) :=
  complexL1OperatorModulus_bandProjectionFn hI T

theorem complexL1BandProjection_idempotent (hI : IsOrderClosedIdeal I)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    complexL1BandProjection hI (complexL1BandProjection hI T) = complexL1BandProjection hI T := by
  apply complexL1Operator_ext <;>
    simp only [complexL1BandProjection_apply,complexL1OperatorRe_bandProjectionFn,
      complexL1OperatorIm_bandProjectionFn,hI.bandProjection_idempotent]

theorem norm_complexL1BandProjection_le_one (hI : IsOrderClosedIdeal I) :
    ‖complexL1BandProjection hI‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun T => by simpa only [one_mul] using norm_complexL1BandProjectionFn_le hI T)

theorem complexL1BandProjection_extension (hI : IsOrderClosedIdeal I) (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    complexL1BandProjection hI (complexL1Extension S) = complexL1Extension (bandProjection hI S) := by
  apply complexL1Operator_ext <;> simp [complexL1BandProjection_apply]

end ThesisCommon
