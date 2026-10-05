import ThesisCommon.Analysis.L1OperatorCountableSup
import ThesisCommon.Analysis.L1CutModulus
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-! A real L1 operator with finite input measure has its entire range in a
single sigma-finite measurable output part. The positive modulus at the
constant-one vector determines that part; no output localizability is needed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem exists_sigmaFinite_range_part
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      ∀ f, T f =ᵐ[ν.restrict Θᶜ] 0 := by
  let R := lOneOperatorModulus T
  let one := lOneIndicator μ univ MeasurableSet.univ
  obtain ⟨Θ, hΘ, hzero, hσ⟩ := (L1.integrable_coeFn (R one)).aefinStronglyMeasurable.exists_set_sigmaFinite
  have hcut0 : lpCut Θᶜ hΘ.compl (R one) = 0 := by
    apply Lp.ext
    have hz := (ae_restrict_iff' hΘ.compl).mp hzero
    filter_upwards [lpCut_coe Θᶜ hΘ.compl (R one), hz, Lp.coeFn_zero ℝ 1 ν] with y hc hy hz'
    rw [hc, hz']
    by_cases hyΘ : y ∈ Θᶜ
    · simp [hyΘ, hy hyΘ]
    · simp [hyΘ]
  have hcutR : (lpCutL Θᶜ hΘ.compl).comp R = 0 := by
    apply positive_lOneOperator_eq_zero_of_one _ _ hcut0
    intro f hf
    change 0 ≤ lpCut Θᶜ hΘ.compl (R f)
    have h := lOneCut_mono Θᶜ hΘ.compl (lOneOperatorModulus_nonneg T f hf)
    change (lpCutL Θᶜ hΘ.compl) 0 ≤ _ at h
    simpa only [map_zero] using h
  refine ⟨Θ, hΘ, hσ, ?_⟩
  intro f
  have hdom : |lpCut Θᶜ hΘ.compl (T f)| ≤ 0 := by
    rw [← lOneCut_abs]
    have h := lOneCut_mono Θᶜ hΘ.compl (lOneOperatorModulus_dominates T f)
    have heq := congrArg (fun U : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν => U |f|) hcutR
    exact h.trans_eq heq
  have hzeroTf : lpCut Θᶜ hΘ.compl (T f) = 0 := by
    apply le_antisymm ((le_abs_self _).trans hdom)
    exact neg_nonpos.mp ((neg_le_abs _).trans hdom)
  have hae := Lp.ext_iff.mp hzeroTf
  change ∀ᵐ y ∂ν.restrict Θᶜ, T f y = 0
  rw [ae_restrict_iff' hΘ.compl]
  filter_upwards [hae, lpCut_coe Θᶜ hΘ.compl (T f), Lp.coeFn_zero ℝ 1 ν] with y hy hc hz
  intro hyΘ
  simpa only [hc, hz, indicator_of_mem hyΘ, Pi.zero_apply] using hy

end ThesisCommon
