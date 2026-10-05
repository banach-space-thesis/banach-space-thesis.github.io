import ThesisCommon.Analysis.ComplexL1OperatorColumns
import ThesisCommon.Analysis.SignedKernelDiagonalTrace

/-! The measurable diagonal and a finite variation envelope for every bounded
complex L1 operator. Complementary operators admit a common measurable set of
positive measure on which one diagonal is bounded below. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [StandardBorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]

def complexL1Diagonal (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (x : X) : ℂ :=
  (realL1Diagonal (complexL1RealColumn T) x : ℂ) +
    Complex.I * (realL1Diagonal (complexL1ImagColumn T) x : ℂ)

@[simp] theorem complexL1Diagonal_re (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (x : X) :
    (complexL1Diagonal T x).re = realL1Diagonal (complexL1RealColumn T) x := by
  simp [complexL1Diagonal]

@[simp] theorem complexL1Diagonal_im (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (x : X) :
    (complexL1Diagonal T x).im = realL1Diagonal (complexL1ImagColumn T) x := by
  simp [complexL1Diagonal]

theorem complexL1Diagonal_measurable (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    Measurable (complexL1Diagonal T) := by
  exact (Complex.measurable_ofReal.comp (realL1Diagonal_measurable _)).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (realL1Diagonal_measurable _)))

theorem complexL1Diagonal_norm_le (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (x : X) :
    ‖complexL1Diagonal T x‖ ≤ 2 * ‖T‖ := by
  calc
    _ ≤ ‖(realL1Diagonal (complexL1RealColumn T) x : ℂ)‖ +
        ‖Complex.I * (realL1Diagonal (complexL1ImagColumn T) x : ℂ)‖ := norm_add_le _ _
    _ = |realL1Diagonal (complexL1RealColumn T) x| +
        |realL1Diagonal (complexL1ImagColumn T) x| := by
      rw [norm_mul, Complex.norm_I, one_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖T‖ + ‖T‖ := add_le_add
      ((realL1Diagonal_abs_le _ x).trans (norm_complexL1RealColumn_le T))
      ((realL1Diagonal_abs_le _ x).trans (norm_complexL1ImagColumn_le T))
    _ = _ := by ring

def complexL1VariationKernel (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) : Kernel X X :=
  (realL1ReverseKernel (complexL1RealColumn T)).variationKernel +
    (realL1ReverseKernel (complexL1ImagColumn T)).variationKernel

instance complexL1VariationKernel_isFinite (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    IsFiniteKernel (complexL1VariationKernel T) := by
  unfold complexL1VariationKernel
  infer_instance

theorem complexL1VariationKernel_real (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (x : X) (A : Set X) :
    (complexL1VariationKernel T x).real A =
      ((realL1ReverseKernel (complexL1RealColumn T)).variationKernel x).real A +
      ((realL1ReverseKernel (complexL1ImagColumn T)).variationKernel x).real A := by
  simp only [complexL1VariationKernel, Kernel.add_apply]
  exact measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)

theorem complexL1Diagonal_re_add_complement (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    ∀ᵐ x ∂μ, (complexL1Diagonal T x).re +
      (complexL1Diagonal (ContinuousLinearMap.id ℂ _ - T) x).re = 1 := by
  simpa only [complexL1Diagonal_re, complexL1RealColumn_complement] using
    realL1Diagonal_add_complement (complexL1RealColumn T)

theorem exists_complexL1Diagonal_large_set
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hμ : μ ≠ 0) :
    ∃ S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ,
      (S = T ∨ S = ContinuousLinearMap.id ℂ _ - T) ∧
      ∃ A : Set X, MeasurableSet A ∧ 0 < μ A ∧
        ∀ x ∈ A, (1 / 2 : ℝ) ≤ ‖complexL1Diagonal S x‖ := by
  let A : Set X := {x | (1 / 2 : ℝ) ≤ (complexL1Diagonal T x).re}
  let B : Set X := {x | (1 / 2 : ℝ) ≤
    (complexL1Diagonal (ContinuousLinearMap.id ℂ _ - T) x).re}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (Complex.measurable_re.comp (complexL1Diagonal_measurable T))
  have hB : MeasurableSet B := measurableSet_le measurable_const
    (Complex.measurable_re.comp (complexL1Diagonal_measurable _))
  have hbnd (S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (x : X)
      (hx : (1 / 2 : ℝ) ≤ (complexL1Diagonal S x).re) :
      (1 / 2 : ℝ) ≤ ‖complexL1Diagonal S x‖ :=
    hx.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  by_cases ha : 0 < μ A
  · exact ⟨T, Or.inl rfl, A, hA, ha, fun x hx => hbnd T x hx⟩
  have haz : μ A = 0 := le_antisymm (le_of_not_gt ha) (zero_le _)
  have hb : 0 < μ B := by
    by_contra hn
    have hbz : μ B = 0 := le_antisymm (le_of_not_gt hn) (zero_le _)
    have haf : ∀ᵐ x ∂μ, x ∉ A := measure_eq_zero_iff_ae_notMem.mp haz
    have hbf : ∀ᵐ x ∂μ, x ∉ B := measure_eq_zero_iff_ae_notMem.mp hbz
    have hf : ∀ᵐ x ∂μ, False := by
      filter_upwards [haf, hbf, complexL1Diagonal_re_add_complement T] with x hx hy he
      have hx' : (complexL1Diagonal T x).re < 1 / 2 := lt_of_not_ge hx
      have hy' : (complexL1Diagonal (ContinuousLinearMap.id ℂ _ - T) x).re < 1 / 2 :=
        lt_of_not_ge hy
      linarith
    exact hμ (Measure.measure_univ_eq_zero.mp (by simpa only [ae_iff, not_false_eq_true,
      Set.setOf_true] using hf))
  exact ⟨ContinuousLinearMap.id ℂ _ - T, Or.inr rfl, B, hB, hb,
    fun x hx => hbnd _ x hx⟩

theorem exists_complexL1Diagonal_localization
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hμ : μ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ,
      (S = T ∨ S = ContinuousLinearMap.id ℂ _ - T) ∧
      ∃ D : Set X, MeasurableSet D ∧ 0 < μ D ∧
        (∀ x ∈ D, (1 / 2 : ℝ) ≤ ‖complexL1Diagonal S x‖) ∧
        ∀ x ∈ D, (complexL1VariationKernel S x).real (D \ {x}) < ε := by
  obtain ⟨S, hS, A, hA, ha, hb⟩ := exists_complexL1Diagonal_large_set T hμ
  obtain ⟨D, hDA, hD, hd, he⟩ :=
    exists_kernel_offDiagonal_small_set (complexL1VariationKernel S) μ hA ha hε
  exact ⟨S, hS, D, hD, hd, fun x hx => hb x (hDA hx), he⟩

end ThesisCommon
