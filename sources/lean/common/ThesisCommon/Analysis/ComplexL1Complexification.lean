import ThesisCommon.Analysis.ComplexL1Coordinates

/-! Complexification of actual real L1 operators. Positivity gives pointwise
modulus domination and equality of the real and complex operator norms. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def complexL1ExtensionReal (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    Lp ℂ 1 μ →L[ℝ] Lp ℂ 1 ν :=
  (complexL1OfReal ν).comp (S.comp (complexL1Re μ)) +
    Complex.I • (complexL1OfReal ν).comp (S.comp (complexL1Im μ))

theorem complexL1ExtensionReal_apply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℂ 1 μ) :
    complexL1ExtensionReal S f = complexL1OfReal ν (S (complexL1Re μ f)) +
      Complex.I • complexL1OfReal ν (S (complexL1Im μ f)) := rfl

@[simp] theorem complexL1Re_extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℂ 1 μ) :
    complexL1Re ν (complexL1ExtensionReal S f) = S (complexL1Re μ f) := by
  simp [complexL1ExtensionReal_apply, complexL1Re_smul]

@[simp] theorem complexL1Im_extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℂ 1 μ) :
    complexL1Im ν (complexL1ExtensionReal S f) = S (complexL1Im μ f) := by
  simp [complexL1ExtensionReal_apply, complexL1Im_smul]

def complexL1Extension (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν where
  toFun := complexL1ExtensionReal S
  map_add' := map_add (complexL1ExtensionReal S)
  map_smul' := by
    intro c f
    apply complexL1_ext
    · simp [complexL1Re_smul]
    · simp [complexL1Im_smul]
  cont := (complexL1ExtensionReal S).continuous

theorem complexL1Extension_apply (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℂ 1 μ) :
    complexL1Extension S f = complexL1ExtensionReal S f := rfl

theorem complexL1Extension_ofReal (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (f : Lp ℝ 1 μ) :
    complexL1Extension S (complexL1OfReal μ f) = complexL1OfReal ν (S f) := by
  simp [complexL1Extension_apply, complexL1ExtensionReal_apply]

theorem complexL1Extension_modulus_le (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) (f : Lp ℂ 1 μ) :
    complexL1Modulus (complexL1Extension S f) ≤ S (complexL1Modulus f) := by
  have hmono : Monotone S := by
    intro a b hab
    have h := hS (b-a) (sub_nonneg.mpr hab)
    rwa [map_sub, sub_nonneg] at h
  apply (complexL1Modulus_isLUB _).2
  rintro _ ⟨c,hc,rfl⟩
  rw [← map_smul, complexL1Extension_apply, complexL1Re_extension]
  exact hmono (complexL1Re_phase_le f c hc.le)

/-- A positive real operator extends with exactly the same operator norm. -/
theorem norm_complexL1Extension_of_positive (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : ∀ f, 0 ≤ f → 0 ≤ S f) : ‖complexL1Extension S‖ = ‖S‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
    intro f
    calc
      ‖complexL1Extension S f‖ = ‖complexL1Modulus (complexL1Extension S f)‖ :=
        (norm_complexL1Modulus _).symm
      _ ≤ ‖S (complexL1Modulus f)‖ := norm_le_norm_of_abs_le_abs (by
        rw [abs_of_nonneg (complexL1Modulus_nonneg _),
          abs_of_nonneg (hS _ (complexL1Modulus_nonneg _))]
        exact complexL1Extension_modulus_le S hS f)
      _ ≤ ‖S‖ * ‖complexL1Modulus f‖ := S.le_opNorm _
      _ = ‖S‖ * ‖f‖ := by rw [norm_complexL1Modulus]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    calc
      ‖S f‖ = ‖complexL1OfReal ν (S f)‖ := (norm_complexL1OfReal _).symm
      _ = ‖complexL1Extension S (complexL1OfReal μ f)‖ := by rw [complexL1Extension_ofReal]
      _ ≤ ‖complexL1Extension S‖ * ‖complexL1OfReal μ f‖ := (complexL1Extension S).le_opNorm _
      _ = ‖complexL1Extension S‖ * ‖f‖ := by rw [norm_complexL1OfReal]

end ThesisCommon
