import NonCalkinAlgebra.RieszCircleBasic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Complex Metric Set
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cauchyTransform (f : ℂ → E) (R : ℝ) (w : ℂ) : E :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, R), (z - w)⁻¹ • f z

theorem cauchyTransform_differentiableOn (f : ℂ → E) (R : ℝ) (hR : 0 < R)
    (hf : CircleIntegrable f 0 R) :
    DifferentiableOn ℂ (cauchyTransform f R) (ball (0 : ℂ) R) := by
  let Rn : NNReal := ⟨R, hR.le⟩
  have hseries := hasFPowerSeriesOn_cauchy_integral (R := Rn) hf (show 0 < Rn from hR)
  simpa only [Metric.emetric_ball_nnreal] using hseries.differentiableOn

theorem cauchyTransform_continuousOn_innerBall (f : ℂ → E) (R r : ℝ)
    (hR : 0 < R) (hrr : r < R) (hf : CircleIntegrable f 0 R) :
    ContinuousOn (cauchyTransform f R) (closedBall (0 : ℂ) r) := by
  apply (cauchyTransform_differentiableOn f R hR hf).continuousOn.mono
  intro w hw
  have hwle : ‖w‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hw
  simpa only [mem_ball, dist_zero_right] using hwle.trans_lt hrr

/-- A Cauchy transform on an outer circle has zero integral over any
strictly smaller concentric circle. This avoids an exchange of two integrals. -/
theorem cauchyTransform_circleIntegral_zero (f : ℂ → E) (R r : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrr : r < R) (hf : CircleIntegrable f 0 R) :
    (∮ w in C(0, r), cauchyTransform f R w) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr (s := ∅) Set.countable_empty (cauchyTransform_continuousOn_innerBall f R r hR hrr hf)
  intro w hw
  have hwin : w ∈ ball (0 : ℂ) R := by
    have hwr : ‖w‖ < r := by simpa only [mem_ball, dist_zero_right] using hw.1
    simpa only [mem_ball, dist_zero_right] using hwr.trans hrr
  exact (cauchyTransform_differentiableOn f R hR hf).differentiableAt (isOpen_ball.mem_nhds hwin)

end NonCalkinAlgebra
