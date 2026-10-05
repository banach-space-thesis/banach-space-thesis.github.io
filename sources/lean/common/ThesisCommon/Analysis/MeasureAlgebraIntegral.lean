import ThesisCommon.Analysis.MeasureAlgebraL1

/-! The arbitrary finite measure-algebra lift preserves the actual
Bochner integral and the constant-one vector. These identities identify
the constant-kernel rank-one operator under conjugation. -/
noncomputable section
open MeasureTheory Set
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSpace Y] [IsFiniteMeasure ν] in
theorem integral_lOneIndicator (a : Set X) (ha : MeasurableSet a) :
    (∫ x, lOneIndicator μ a ha x ∂μ) = (μ a).toReal := by
  rw [integral_congr_ae (lOneIndicator_coe a ha), integral_indicator ha, integral_const]
  simp [Measure.real]

namespace MeasureAlgebraIso
variable (Φ : MeasureAlgebraIso μ ν)

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem map_univ :
    Φ.toEquiv (MeasureAlgebra.mk μ univ MeasurableSet.univ) =
      MeasureAlgebra.mk ν univ MeasurableSet.univ := by
  have h := Φ.map_iInter (fun _ : Empty => MeasureAlgebra.mk μ univ MeasurableSet.univ)
  simpa only [MeasureAlgebra.iInter, iInter_of_empty] using h

omit [IsFiniteMeasure ν] in
theorem isFiniteMeasure_of_source (Φ : MeasureAlgebraIso μ ν) : IsFiniteMeasure ν where
  measure_univ_lt_top := by
    have h := Φ.measure_eq (MeasureAlgebra.mk μ univ MeasurableSet.univ)
    rw [Φ.map_univ] at h
    change ν univ = μ univ at h
    rw [h]
    exact measure_lt_top μ univ

theorem lOneEquiv_one :
    Φ.lOneEquiv (lOneIndicator μ univ MeasurableSet.univ) =
      lOneIndicator ν univ MeasurableSet.univ :=
  Φ.lOneEquiv_indicator_of_mk_eq univ MeasurableSet.univ univ MeasurableSet.univ Φ.map_univ

theorem integral_lOneEquiv (f : Lp ℝ 1 μ) :
    (∫ y, Φ.lOneEquiv f y ∂ν) = ∫ x, f x ∂μ := by
  have heq : (L1.integralCLM : Lp ℝ 1 ν →L[ℝ] ℝ).comp Φ.lOneMap =
      (L1.integralCLM : Lp ℝ 1 μ →L[ℝ] ℝ) := by
    apply lOne_continuousLinearMap_ext_indicators
    intro a ha
    rw [ContinuousLinearMap.comp_apply, Φ.lOneMap_indicator]
    rw [← L1.integral_eq, ← L1.integral_eq, L1.integral_eq_integral, L1.integral_eq_integral]
    rw [integral_lOneIndicator, integral_lOneIndicator, Φ.measure_imageSet a ha]
  have hf := DFunLike.congr_fun heq f
  change L1.integralCLM (Φ.lOneMap f) = L1.integralCLM f at hf
  rw [← L1.integral_eq, ← L1.integral_eq, L1.integral_eq_integral, L1.integral_eq_integral] at hf
  exact hf

theorem lOneEquiv_symm_eq : Φ.symm.lOneEquiv = Φ.lOneEquiv.symm := by
  apply LinearIsometryEquiv.ext
  intro f
  exact (Φ.lOneEquiv_symm_apply f).symm

theorem integral_lOneEquiv_symm (f : Lp ℝ 1 ν) :
    (∫ x, Φ.lOneEquiv.symm f x ∂μ) = ∫ y, f y ∂ν := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (Φ.integral_lOneEquiv (Φ.lOneEquiv.symm f)).symm

end MeasureAlgebraIso
end ThesisCommon
