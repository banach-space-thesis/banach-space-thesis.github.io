import ThesisCommon.Analysis.ComplexL1OperatorColumns
import ThesisCommon.Analysis.LpBoundedMultiplier

/-! Real columns commute with genuine measurable cuts. Multipliers retain
their real and imaginary pointwise formulas on the L1 quotient. -/
noncomputable section
open MeasureTheory Filter Set
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

@[simp] theorem complexL1Re_cut (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 1 μ) :
    complexL1Re μ (lpCut D hD f) = lpCut D hD (complexL1Re μ f) := by
  apply Lp.ext
  filter_upwards [complexL1Re_coe (lpCut D hD f), lpCut_coe D hD f,
    lpCut_coe D hD (complexL1Re μ f), complexL1Re_coe f] with x h₁ h₂ h₃ h₄
  by_cases hx : x ∈ D <;> simp [h₁, h₂, h₃, h₄, hx]

@[simp] theorem complexL1Im_cut (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 1 μ) :
    complexL1Im μ (lpCut D hD f) = lpCut D hD (complexL1Im μ f) := by
  apply Lp.ext
  filter_upwards [complexL1Im_coe (lpCut D hD f), lpCut_coe D hD f,
    lpCut_coe D hD (complexL1Im μ f), complexL1Im_coe f] with x h₁ h₂ h₃ h₄
  by_cases hx : x ∈ D <;> simp [h₁, h₂, h₃, h₄, hx]

@[simp] theorem complexL1_cut_ofReal (D : Set X) (hD : MeasurableSet D) (f : Lp ℝ 1 μ) :
    lpCut D hD (complexL1OfReal μ f) = complexL1OfReal μ (lpCut D hD f) := by
  apply Lp.ext
  filter_upwards [lpCut_coe D hD (complexL1OfReal μ f), complexL1OfReal_coe f,
    complexL1OfReal_coe (lpCut D hD f), lpCut_coe D hD f] with x h₁ h₂ h₃ h₄
  by_cases hx : x ∈ D <;> simp [h₁, h₂, h₃, h₄, hx]

@[simp] theorem complexL1RealColumn_sub (S T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    complexL1RealColumn (S - T) = complexL1RealColumn S - complexL1RealColumn T := by
  ext f
  simp

@[simp] theorem complexL1ImagColumn_sub (S T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    complexL1ImagColumn (S - T) = complexL1ImagColumn S - complexL1ImagColumn T := by
  ext f
  simp

@[simp] theorem complexL1RealColumn_cut (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (D : Set X) (hD : MeasurableSet D) :
    complexL1RealColumn ((lpCutL D hD).comp (T.comp (lpCutL D hD))) =
      (lpCutL D hD).comp ((complexL1RealColumn T).comp (lpCutL D hD)) := by
  ext f : 1
  change complexL1Re μ (lpCut D hD (T (lpCut D hD (complexL1OfReal μ f)))) =
    lpCut D hD (complexL1Re μ (T (complexL1OfReal μ (lpCut D hD f))))
  rw [complexL1Re_cut, complexL1_cut_ofReal]

@[simp] theorem complexL1ImagColumn_cut (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (D : Set X) (hD : MeasurableSet D) :
    complexL1ImagColumn ((lpCutL D hD).comp (T.comp (lpCutL D hD))) =
      (lpCutL D hD).comp ((complexL1ImagColumn T).comp (lpCutL D hD)) := by
  ext f : 1
  change complexL1Im μ (lpCut D hD (T (lpCut D hD (complexL1OfReal μ f)))) =
    lpCut D hD (complexL1Im μ (T (complexL1OfReal μ (lpCut D hD f))))
  rw [complexL1Im_cut, complexL1_cut_ofReal]

theorem complexL1RealColumn_multiplier_coe (g : X → ℂ)
    (hg : AEStronglyMeasurable g μ) (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℝ 1 μ) :
    complexL1RealColumn (lpBoundedMultiplier (p := 1) g hg C hb) f =ᵐ[μ]
      fun x => (g x).re * f x := by
  filter_upwards [complexL1Re_coe (lpBoundedMultiplier (p := 1) g hg C hb
      (complexL1OfReal μ f)), lpBoundedMultiplier_coe g hg C hb (complexL1OfReal μ f),
    complexL1OfReal_coe f] with x hr hm hf
  change (complexL1Re μ (lpBoundedMultiplier g hg C hb (complexL1OfReal μ f))) x = _
  rw [hr, hm, hf]
  simp

theorem complexL1ImagColumn_multiplier_coe (g : X → ℂ)
    (hg : AEStronglyMeasurable g μ) (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℝ 1 μ) :
    complexL1ImagColumn (lpBoundedMultiplier (p := 1) g hg C hb) f =ᵐ[μ]
      fun x => (g x).im * f x := by
  filter_upwards [complexL1Im_coe (lpBoundedMultiplier (p := 1) g hg C hb
      (complexL1OfReal μ f)), lpBoundedMultiplier_coe g hg C hb (complexL1OfReal μ f),
    complexL1OfReal_coe f] with x hr hm hf
  change (complexL1Im μ (lpBoundedMultiplier g hg C hb (complexL1OfReal μ f))) x = _
  rw [hr, hm, hf]
  simp

end ThesisCommon
