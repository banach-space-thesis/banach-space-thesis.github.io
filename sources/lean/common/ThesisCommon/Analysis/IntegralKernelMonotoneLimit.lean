import ThesisCommon.Analysis.IntegralKernel
import Mathlib.Topology.Order.MonotoneConvergence

/-! Monotone convergence of nonnegative kernels with a uniform column
bound. The extended-real supremum is proved finite almost everywhere before
it is converted to a real kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite ν]

theorem exists_monotone_kernel_limit (k : ℕ → X × Y → ℝ)
    (hkm : ∀ n, Measurable (k n))
    (hkpos : ∀ n, ∀ᵐ z ∂μ.prod ν, 0 ≤ k n z)
    (hkmono : ∀ n, k n ≤ᵐ[μ.prod ν] k (n + 1))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, HasKernelBound μ ν (k n) C) :
    ∃ r : X × Y → ℝ, Measurable r ∧ (∀ z, 0 ≤ r z) ∧ HasKernelBound μ ν r C ∧
      ∀ᵐ z ∂μ.prod ν, (∀ n, k n z ≤ r z) ∧
        Tendsto (fun n => k n z) atTop (𝓝 (r z)) := by
  let F : X × Y → ℝ≥0∞ := fun z => ⨆ n, ENNReal.ofReal (k n z)
  have hFm : Measurable F := Measurable.iSup fun n => (hkm n).ennreal_ofReal
  have hcolumns : ∀ᵐ x ∂μ, (∫⁻ y, F (x, y) ∂ν) ≤ ENNReal.ofReal C := by
    have hm := (ae_all_iff.mpr fun n => Measure.ae_ae_of_ae_prod (hkmono n))
    filter_upwards [ae_all_iff.mpr hbound, hm] with x hx hmx
    dsimp only [F]
    rw [lintegral_iSup_ae (f := fun n y => ENNReal.ofReal (k n (x, y)))
      (fun n => ((hkm n).comp measurable_prodMk_left).ennreal_ofReal)
      (fun n => (hmx n).mono fun y hy => ENNReal.ofReal_le_ofReal hy)]
    apply iSup_le
    intro n
    calc
      (∫⁻ y, ENNReal.ofReal (k n (x, y)) ∂ν) ≤
          ∫⁻ y, ENNReal.ofReal ‖k n (x, y)‖ ∂ν :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (by
          rw [Real.norm_eq_abs]; exact le_abs_self _)
      _ = ENNReal.ofReal (∫ y, ‖k n (x, y)‖ ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal (hx n).1.norm
          (Eventually.of_forall fun _ => norm_nonneg _)).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hx n).2
  have hfinite : ∀ᵐ z ∂μ.prod ν, F z < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt hFm measurable_const)).mpr
    filter_upwards [hcolumns] with x hx
    exact ae_lt_top (hFm.comp measurable_prodMk_left)
      ((lt_of_le_of_lt hx ENNReal.ofReal_lt_top).ne)
  let r : X × Y → ℝ := fun z => (F z).toReal
  have hrm : Measurable r := hFm.ennreal_toReal
  have hrpos : ∀ z, 0 ≤ r z := fun _ => ENNReal.toReal_nonneg
  have hrbound : HasKernelBound μ ν r C := by
    filter_upwards [hcolumns] with x hx
    have hxfin : (∫⁻ y, F (x, y) ∂ν) ≠ ∞ :=
      (lt_of_le_of_lt hx ENNReal.ofReal_lt_top).ne
    have hxm : Measurable (fun y => F (x, y)) := hFm.comp measurable_prodMk_left
    refine ⟨integrable_toReal_of_lintegral_ne_top hxm.aemeasurable hxfin, ?_⟩
    calc
      (∫ y, ‖r (x, y)‖ ∂ν) = ∫ y, (F (x, y)).toReal ∂ν := by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hrpos _), r]
      _ = (∫⁻ y, F (x, y) ∂ν).toReal := integral_toReal hxm.aemeasurable (ae_lt_top hxm hxfin)
      _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
      _ = C := ENNReal.toReal_ofReal hC
  refine ⟨r, hrm, hrpos, hrbound, ?_⟩
  filter_upwards [hfinite, ae_all_iff.mpr hkpos, ae_all_iff.mpr hkmono] with z hz hpos hmono
  have hmon : Monotone (fun n => ENNReal.ofReal (k n z)) :=
    monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n)
  constructor
  · intro n
    calc
      k n z = (ENNReal.ofReal (k n z)).toReal := (ENNReal.toReal_ofReal (hpos n)).symm
      _ ≤ (F z).toReal := ENNReal.toReal_mono hz.ne (le_iSup (fun n => ENNReal.ofReal (k n z)) n)
  · have ht := (ENNReal.tendsto_toReal hz.ne).comp (tendsto_atTop_iSup hmon)
    change Tendsto (fun n => (ENNReal.ofReal (k n z)).toReal) atTop (𝓝 (r z)) at ht
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hpos _)] using ht

end ThesisCommon
