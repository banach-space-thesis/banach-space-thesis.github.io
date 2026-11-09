import SurveyStatements.P1ComplexCoefficients
import SurveyStatements.P1Definitions
import Mathlib.Analysis.Normed.Module.Dual

/-! The finite complex cancellation estimate in Behrends's quantitative
Rosenthal proof.  All coefficients, vectors, and separating functionals in
the statement are actual data. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem complex_pattern_coefficient_estimate {ι : Type*} [DecidableEq ι] (F S : Finset ι)
    (hSF : S ⊆ F) (a : ι → ℂ) (x : ι → X) (f : X →L[ℂ] ℂ)
    (hf : ‖f‖ ≤ 1) (z w : ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmass : (∑ i ∈ F, ‖a i‖) = 1)
    (hsum : ‖∑ i ∈ F, a i‖ ≤ τ)
    (hS : (1 / 4 : ℝ) ≤ ‖∑ i ∈ S, a i‖)
    (hpattern : ∀ i ∈ F, ‖f (x i) - (z + if i ∈ S then w else 0)‖ ≤ τ) :
    ‖w‖ / 4 ≤ ‖∑ i ∈ F, a i • x i‖ + (1 + ‖z‖) * τ := by
  classical
  let g : ℂ := ∑ i ∈ F, a i * f (x i)
  let t : ℂ := (∑ i ∈ F, a i) * z + (∑ i ∈ S, a i) * w
  have ht : t = ∑ i ∈ F, a i * (z + if i ∈ S then w else 0) := by
    have hif : (∑ i ∈ F, if i ∈ S then a i * w else 0) = ∑ i ∈ S, a i * w := by
      calc
        _ = ∑ i ∈ S, if i ∈ S then a i * w else 0 := by
          symm
          apply Finset.sum_subset hSF
          intro i _ hi
          simp only [hi, if_false]
        _ = ∑ i ∈ S, a i * w := Finset.sum_congr rfl (fun i hi => by simp only [hi, if_true])
    simp only [t, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      hif, ← Finset.sum_mul]
  have herr : ‖g - t‖ ≤ τ := by
    rw [ht]
    change ‖(∑ i ∈ F, a i * f (x i)) - ∑ i ∈ F, a i * (z + if i ∈ S then w else 0)‖ ≤ τ
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ F, ‖a i * f (x i) - a i * (z + if i ∈ S then w else 0)‖ := norm_sum_le _ _
      _ = ∑ i ∈ F, ‖a i‖ * ‖f (x i) - (z + if i ∈ S then w else 0)‖ := by
        simp only [← mul_sub, norm_mul]
      _ ≤ ∑ i ∈ F, ‖a i‖ * τ :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hpattern i hi) (norm_nonneg _))
      _ = τ := by rw [← Finset.sum_mul, hmass, one_mul]
  have hg : ‖g‖ ≤ ‖∑ i ∈ F, a i • x i‖ := by
    have heq : f (∑ i ∈ F, a i • x i) = g := by
      simp only [map_sum, map_smul, smul_eq_mul, g]
    rw [← heq]
    have hupper := mul_le_mul_of_nonneg_right hf (norm_nonneg (∑ i ∈ F, a i • x i))
    simp only [one_mul] at hupper
    exact (f.le_opNorm _).trans hupper
  have htupper : ‖t‖ ≤ ‖g‖ + τ := by
    have h := norm_add_le g (t - g)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add_left (by simpa only [norm_sub_rev] using herr) _)
  have hz : ‖(∑ i ∈ F, a i) * z‖ ≤ τ * ‖z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hcomp : ‖(∑ i ∈ S, a i) * w‖ ≤ ‖t‖ + ‖(∑ i ∈ F, a i) * z‖ := by
    have h := norm_sub_le t ((∑ i ∈ F, a i) * z)
    have heq : t - (∑ i ∈ F, a i) * z = (∑ i ∈ S, a i) * w := by
      dsimp [t]
      ring
    simpa only [heq] using h
  have hlow : ‖w‖ / 4 ≤ ‖(∑ i ∈ S, a i) * w‖ := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right hS (norm_nonneg w)
    nlinarith
  nlinarith

theorem exists_complex_pattern_coefficient_estimate {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (a : ι → ℂ) (x : ι → X) {τ D M : ℝ} (hτ : 0 ≤ τ)
    (hmass : (∑ i ∈ F, ‖a i‖) = 1) (hsum : ‖∑ i ∈ F, a i‖ ≤ τ)
    (hpatterns : ∀ S : Finset ι, S ⊆ F →
      ∃ f : X →L[ℂ] ℂ, ∃ z w : ℂ, ‖f‖ ≤ 1 ∧ ‖z‖ ≤ M ∧ D ≤ ‖w‖ ∧
        ∀ i ∈ F, ‖f (x i) - (z + if i ∈ S then w else 0)‖ ≤ τ) :
    D / 4 ≤ ‖∑ i ∈ F, a i • x i‖ + (1 + M) * τ := by
  obtain ⟨S, hSF, hS⟩ := exists_complex_unit_mass_subset F a hmass
  obtain ⟨f, z, w, hf, hz, hw, hp⟩ := hpatterns S hSF
  have h := complex_pattern_coefficient_estimate F S hSF a x f hf z w hτ hmass hsum hS hp
  have hzτ := mul_le_mul_of_nonneg_right hz hτ
  linarith

end SurveyStatements.P1
