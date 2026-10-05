import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecificLimits.Normed

/-! A geometrically small family with unchanged positive support has a
nonzero member fitting below every nonzero positive measurable budget on
a set of positive measure.  No uniform positive lower bound on the budget
is assumed. -/
open MeasureTheory Set Filter Topology
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_positive_measure_conditional_increment
    (f : ℕ → X → ℝ) (q h : X → ℝ)
    (hbudget : ∀ᵐ x ∂μ, 0 ≤ h x ∧ h x ≤ q x) (hne : ¬ h =ᵐ[μ] 0)
    (hpos : ∀ n, ∀ᵐ x ∂μ, 0 < q x → 0 < f n x)
    (hbound : ∀ n, ∀ᵐ x ∂μ, f n x ≤ (1/2 : ℝ)^n * q x) :
    ∃ n : ℕ, μ {x | 0 < f n x ∧ f n x ≤ h x} ≠ 0 := by
  by_contra hbad
  push_neg at hbad
  have htest : ∀ n, ∀ᵐ x ∂μ, ¬ (0 < f n x ∧ f n x ≤ h x) := by
    intro n
    exact measure_eq_zero_iff_ae_notMem.mp (hbad n)
  apply hne
  filter_upwards [hbudget, ae_all_iff.mpr hpos, ae_all_iff.mpr hbound,
    ae_all_iff.mpr htest] with x hx hp hb ht
  change h x = 0
  apply le_antisymm ?_ hx.1
  have hl : Tendsto (fun n : ℕ => (1/2 : ℝ)^n * q x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) < 1)).mul_const (q x)
  by_contra hh
  have hhp : 0 < h x := lt_of_not_ge hh
  have hqp : 0 < q x := hhp.trans_le hx.2
  have hle : h x ≤ 0 := ge_of_tendsto' hl (fun n => by
    have hfn : h x < f n x := lt_of_not_ge (fun hfn => ht n ⟨hp n hqp, hfn⟩)
    exact hfn.le.trans (hb n))
  exact hhp.not_ge hle

end ThesisCommon

