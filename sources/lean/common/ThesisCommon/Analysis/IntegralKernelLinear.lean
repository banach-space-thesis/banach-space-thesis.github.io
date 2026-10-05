import ThesisCommon.Analysis.IntegralKernelOrder

/-! The real integral operators form an actual linear subspace of bounded
operators. Kernel formulas prove closure, with no representation axiom. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k h : X × Y → ℝ} {K H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem isIntegralKernel_zero : IsIntegralKernel (fun _ : X × Y => (0 : ℝ))
    (0 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) where
  measurable := measurable_const
  integrable_section f := Eventually.of_forall fun _ => by simp
  represents f := by simpa only [zero_mul, integral_zero, ContinuousLinearMap.zero_apply] using Lp.coeFn_zero ℝ 1 ν

theorem IsIntegralKernel.add (hk : IsIntegralKernel k K) (hh : IsIntegralKernel h H) :
    IsIntegralKernel (fun z => k z + h z) (K + H) where
  measurable := hk.measurable.add hh.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_section f, hh.integrable_section f] with y hy hy'
    simpa only [add_mul] using hy.add hy'
  represents f := by
    filter_upwards [hk.represents f, hh.represents f, Lp.coeFn_add (K f) (H f),
      hk.integrable_section f, hh.integrable_section f] with y hy hy' hadd hi hi'
    change (K f + H f) y = _
    rw [hadd, Pi.add_apply, hy, hy', ← integral_add hi hi']
    simp only [add_mul]

theorem IsIntegralKernel.smul (hk : IsIntegralKernel k K) (a : ℝ) :
    IsIntegralKernel (fun z => a * k z) (a • K) where
  measurable := measurable_const.mul hk.measurable
  integrable_section f := by
    filter_upwards [hk.integrable_section f] with y hy
    simpa only [mul_assoc] using hy.const_mul a
  represents f := by
    filter_upwards [hk.represents f, Lp.coeFn_smul a (K f)] with y hy hs
    change (a • K f) y = _
    rw [hs, Pi.smul_apply, smul_eq_mul, hy, ← integral_const_mul]
    simp only [mul_assoc]

theorem isIntegralOperator_zero : IsIntegralOperator (0 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :=
  ⟨_, isIntegralKernel_zero⟩

theorem IsIntegralOperator.add (hK : IsIntegralOperator K) (hH : IsIntegralOperator H) :
    IsIntegralOperator (K + H) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨h, hh⟩ := hH
  exact ⟨_, hk.add hh⟩

theorem IsIntegralOperator.sub (hK : IsIntegralOperator K) (hH : IsIntegralOperator H) :
    IsIntegralOperator (K - H) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨h, hh⟩ := hH
  exact ⟨_, hk.sub hh⟩

theorem IsIntegralOperator.smul (hK : IsIntegralOperator K) (a : ℝ) :
    IsIntegralOperator (a • K) := by
  obtain ⟨k, hk⟩ := hK
  exact ⟨_, hk.smul a⟩

def integralOperatorSubmodule (μ : Measure X) (ν : Measure Y) :
    Submodule ℝ (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) where
  carrier := {K | IsIntegralOperator K}
  zero_mem' := isIntegralOperator_zero
  add_mem' := fun hK hH => hK.add hH
  smul_mem' := fun a _ hK => hK.smul a

end ThesisCommon
