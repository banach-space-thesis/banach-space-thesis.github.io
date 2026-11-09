import SurveyStatements.P1C0FiniteCoefficients
import Mathlib.Analysis.Complex.Basic

/-! A norming functional for a nearly maximal c₀ tail block has small
values on every coefficient-unit block disjoint from it. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem c0Finsupp_add_phase_unit_coefficients (b d : ℕ →₀ ℂ)
    (hdisjoint : Disjoint b.support d.support)
    (hb : ∀ i, ‖b i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    {θ : ℂ} (hθ : ‖θ‖ = 1) : ∀ i, ‖(b + θ • d) i‖ ≤ 1 := by
  classical
  intro i
  by_cases hbi : i ∈ b.support
  · have hdi : i ∉ d.support := fun hdi => Finset.disjoint_left.mp hdisjoint hbi hdi
    simpa [Finsupp.notMem_support_iff.mp hdi] using hb i
  · simpa [Finsupp.notMem_support_iff.mp hbi, norm_mul, hθ] using hd i

theorem c0_normingFunctional_offBlock_bound (T : ComplexC0 →L[ℂ] X)
    (N : ℕ) (b d : ℕ →₀ ℂ)
    (hbsupp : ∀ i ∈ b.support, N ≤ i) (hdsupp : ∀ i ∈ d.support, N ≤ i)
    (hb : ∀ i, ‖b i‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1)
    (hdisjoint : Disjoint b.support d.support)
    (f : X →L[ℂ] ℂ) (hfnorm : ‖f‖ = 1)
    (hfvalue : f (T (c0Finsupp b)) = (‖T (c0Finsupp b)‖ : ℂ)) :
    ‖f (T (c0Finsupp d))‖ ≤ c0TailUpperNorm T N - ‖T (c0Finsupp b)‖ := by
  classical
  obtain ⟨θ, hθ, hθeq⟩ := Complex.exists_norm_eq_mul_self (f (T (c0Finsupp d)))
  let c : ℕ →₀ ℂ := b + θ • d
  have hcsupp : ∀ i ∈ c.support, N ≤ i := by
    intro i hi
    have hiunion := Finsupp.support_add hi
    rcases Finset.mem_union.mp hiunion with hbi | hdi
    · exact hbsupp i hbi
    · exact hdsupp i (Finsupp.support_smul hdi)
  have hcunit : ∀ i, ‖c i‖ ≤ 1 := c0Finsupp_add_phase_unit_coefficients b d hdisjoint hb hd hθ
  have hcmap : c0Finsupp c = c0Finsupp b + θ • c0Finsupp d := by
    ext i
    rfl
  have heval : f (T (c0Finsupp c)) =
      ((‖T (c0Finsupp b)‖ + ‖f (T (c0Finsupp d))‖ : ℝ) : ℂ) := by
    simp only [hcmap, map_add, map_smul, smul_eq_mul, hfvalue, ← hθeq, Complex.ofReal_add]
  have hfnormbound : ‖f (T (c0Finsupp c))‖ ≤ ‖T (c0Finsupp c)‖ := by
    simpa [hfnorm] using f.le_opNorm (T (c0Finsupp c))
  have hnorm : ‖T (c0Finsupp b)‖ + ‖f (T (c0Finsupp d))‖ ≤ ‖T (c0Finsupp c)‖ := by
    rw [heval, Complex.norm_real, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      at hfnormbound
    exact hfnormbound
  have hbound := norm_c0Finsupp_image_le_tail T N c hcsupp hcunit
  linarith

end SurveyStatements.P1
