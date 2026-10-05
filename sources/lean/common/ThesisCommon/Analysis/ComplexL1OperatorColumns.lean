import ThesisCommon.Analysis.ComplexL1Complexification

/-! The two real columns of an arbitrary complex L1 operator, and its exact
reconstruction by complexification. No positivity hypothesis is imposed. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem norm_complexL1Re_le (f : Lp ℂ 1 μ) : ‖complexL1Re μ f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [complexL1Re_coe f] with x hx
  rw [hx, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem norm_complexL1Im_le (f : Lp ℂ 1 μ) : ‖complexL1Im μ f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [complexL1Im_coe f] with x hx
  rw [hx, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm _

def complexL1RealColumn (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (complexL1Re ν).comp ((T.restrictScalars ℝ).comp (complexL1OfReal μ))

def complexL1ImagColumn (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (complexL1Im ν).comp ((T.restrictScalars ℝ).comp (complexL1OfReal μ))

@[simp] theorem complexL1RealColumn_apply (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (f : Lp ℝ 1 μ) : complexL1RealColumn T f = complexL1Re ν (T (complexL1OfReal μ f)) := rfl

@[simp] theorem complexL1ImagColumn_apply (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν)
    (f : Lp ℝ 1 μ) : complexL1ImagColumn T f = complexL1Im ν (T (complexL1OfReal μ f)) := rfl

theorem norm_complexL1RealColumn_le (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖complexL1RealColumn T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  exact (norm_complexL1Re_le _).trans ((T.le_opNorm _).trans_eq (congrArg (fun r : ℝ => ‖T‖ * r) (norm_complexL1OfReal f)))

theorem norm_complexL1ImagColumn_le (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖complexL1ImagColumn T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  exact (norm_complexL1Im_le _).trans ((T.le_opNorm _).trans_eq (congrArg (fun r : ℝ => ‖T‖ * r) (norm_complexL1OfReal f)))

@[simp] theorem complexL1RealColumn_complement (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    complexL1RealColumn (ContinuousLinearMap.id ℂ _ - T) =
      ContinuousLinearMap.id ℝ _ - complexL1RealColumn T := by
  ext f
  simp

theorem complexL1_operator_ofReal (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (f : Lp ℝ 1 μ) :
    T (complexL1OfReal μ f) = complexL1OfReal ν (complexL1RealColumn T f) +
      Complex.I • complexL1OfReal ν (complexL1ImagColumn T f) :=
  (complexL1_decomposition _).symm

theorem complexL1_operator_reconstruction (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    T = complexL1Extension (complexL1RealColumn T) +
      Complex.I • complexL1Extension (complexL1ImagColumn T) := by
  ext f : 1
  rw [← complexL1_decomposition f]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, complexL1Extension_ofReal]
  rw [complexL1_operator_ofReal, complexL1_operator_ofReal]

theorem norm_complexL1Extension_le (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ‖complexL1Extension S‖ ≤ 2 * ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖complexL1OfReal ν (S (complexL1Re μ f)) +
    Complex.I • complexL1OfReal ν (S (complexL1Im μ f))‖ ≤ _
  calc
    _ ≤ ‖complexL1OfReal ν (S (complexL1Re μ f))‖ +
        ‖Complex.I • complexL1OfReal ν (S (complexL1Im μ f))‖ := norm_add_le _ _
    _ = ‖S (complexL1Re μ f)‖ + ‖S (complexL1Im μ f)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul, norm_complexL1OfReal, norm_complexL1OfReal]
    _ ≤ ‖S‖ * ‖f‖ + ‖S‖ * ‖f‖ := add_le_add
      ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_complexL1Re_le f) (norm_nonneg S)))
      ((S.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_complexL1Im_le f) (norm_nonneg S)))
    _ = _ := by ring

theorem norm_complexL1Operator_le_columns (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) :
    ‖T‖ ≤ 2 * ‖complexL1RealColumn T‖ + 2 * ‖complexL1ImagColumn T‖ := by
  calc
    ‖T‖ = ‖complexL1Extension (complexL1RealColumn T) +
        Complex.I • complexL1Extension (complexL1ImagColumn T)‖ :=
      congrArg norm (complexL1_operator_reconstruction T)
    _ ≤ ‖complexL1Extension (complexL1RealColumn T)‖ +
        ‖Complex.I • complexL1Extension (complexL1ImagColumn T)‖ := norm_add_le _ _
    _ = ‖complexL1Extension (complexL1RealColumn T)‖ +
        ‖complexL1Extension (complexL1ImagColumn T)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ _ := add_le_add (norm_complexL1Extension_le _) (norm_complexL1Extension_le _)

end ThesisCommon
