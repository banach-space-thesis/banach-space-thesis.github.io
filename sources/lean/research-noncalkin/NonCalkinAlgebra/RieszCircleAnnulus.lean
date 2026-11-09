import NonCalkinAlgebra.RieszCircleBasic
import Mathlib.Analysis.Normed.Algebra.Spectrum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open Metric Set
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A resolvent circle has a larger concentric resolvent circle with no
spectrum in the entire closed annulus between them. -/
theorem exists_larger_resolvent_annulus (a : A) (r : ℝ)
    (hcircle : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ a) :
    ∃ R : ℝ, r < R ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → z ∈ resolventSet ℂ a := by
  let S : Set ℝ := norm '' spectrum ℂ a
  have hS : IsClosed S := ((spectrum.isCompact a).image continuous_norm).isClosed
  have hrS : r ∉ S := by
    rintro ⟨z, hzs, hzr⟩
    exact hzs (hcircle z hzr)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl r hrS
  refine ⟨r + δ / 2, by linarith, ?_⟩
  intro z hlow hupp
  have hnear : ‖z‖ ∈ ball r δ := by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlow)]
    linarith
  have hnot : z ∉ spectrum ℂ a := fun hz => (hball hnear) ⟨z, hz, rfl⟩
  exact spectrum.notMem_iff.mp hnot

theorem rieszCircle_eq_of_resolvent_annulus (a : A) (r R : ℝ) (hr : 0 < r) (hle : r ≤ R)
    (hannulus : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → z ∈ resolventSet ℂ a) :
    rieszCircle a R = rieszCircle a r := by
  have hc : ContinuousOn (resolvent a) (closedBall (0 : ℂ) R \ ball 0 r) := by
    intro z hz
    have hupp : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz.1
    have hlow : r ≤ ‖z‖ := by
      have hn : ¬ ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz.2
      exact le_of_not_gt hn
    exact (resolvent_hasDerivAt (hannulus z hlow hupp)).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (ball (0 : ℂ) R \ closedBall 0 r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (resolvent a) z := by
    intro z hz
    have hupp : ‖z‖ ≤ R := by
      exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz.1.1)
    have hlow : r ≤ ‖z‖ := by
      have hn : ¬ ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz.1.2
      exact (lt_of_not_ge hn).le
    exact (resolvent_hasDerivAt (hannulus z hlow hupp)).differentiableAt
  unfold rieszCircle
  exact congrArg (fun x : A => (2 * Real.pi * Complex.I : ℂ)⁻¹ • x)
    (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr hle Set.countable_empty hc hd)

end NonCalkinAlgebra
