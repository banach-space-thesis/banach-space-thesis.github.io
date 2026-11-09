import SurveyStatements.P1L1Tail

/-! Finite unit-mass blocks in the complex Rosenthal alternative.  Failure
of an actual positive lower ℓ₁ estimate is equivalent to arbitrarily small
finite blocks, by explicit normalization of their coefficients. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem bounded_sequence_upper_l1_estimate (e : ℕ → X) {M : ℝ}
    (hM : ∀ n, ‖e n‖ ≤ M) (b : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ e b‖ ≤ M * coefficientL1Mass b := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ i ∈ b.support, b i • e i‖ ≤ ∑ i ∈ b.support, ‖b i • e i‖ := norm_sum_le _ _
    _ = ∑ i ∈ b.support, ‖b i‖ * ‖e i‖ := by simp only [norm_smul]
    _ ≤ ∑ i ∈ b.support, ‖b i‖ * M :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _))
    _ = M * coefficientL1Mass b := by
      change (∑ i ∈ b.support, ‖b i‖ * M) = M * ∑ i ∈ b.support, ‖b i‖
      rw [← Finset.sum_mul, mul_comm]

theorem no_lower_l1_estimate_exists_small_unit_mass_block (e : ℕ → X)
    (hno : ¬ ∃ L : ℝ, 0 < L ∧ ∀ b : ℕ →₀ ℂ,
      L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℕ →₀ ℂ, coefficientL1Mass b = 1 ∧
      ‖Finsupp.linearCombination ℂ e b‖ < ε := by
  classical
  have hbad : ¬ ∀ b : ℕ →₀ ℂ,
      ε * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖ := by
    intro h
    exact hno ⟨ε, hε, h⟩
  push_neg at hbad
  obtain ⟨b, hb⟩ := hbad
  have hmass : 0 < coefficientL1Mass b := by
    have : 0 < ε * coefficientL1Mass b := (norm_nonneg _).trans_lt hb
    have hpos := (mul_pos_iff.mp this).resolve_right
      (by intro h; exact (not_lt_of_ge hε.le) h.1)
    exact hpos.2
  let z : ℂ := ((coefficientL1Mass b : ℝ) : ℂ)⁻¹
  have hz : ‖z‖ = (coefficientL1Mass b)⁻¹ := by
    simp only [z, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmass]
  refine ⟨z • b, ?_, ?_⟩
  · rw [coefficientL1Mass_smul, hz, inv_mul_cancel₀ hmass.ne']
  · rw [map_smul, norm_smul, hz]
    exact (inv_mul_lt_iff₀' hmass).mpr hb

theorem no_lower_l1_estimate_iff_small_unit_mass_blocks (e : ℕ → X) :
    (¬ ∃ L : ℝ, 0 < L ∧ ∀ b : ℕ →₀ ℂ,
      L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ e b‖) ↔
    ∀ ε : ℝ, 0 < ε → ∃ b : ℕ →₀ ℂ, coefficientL1Mass b = 1 ∧
      ‖Finsupp.linearCombination ℂ e b‖ < ε := by
  constructor
  · exact fun h ε hε => no_lower_l1_estimate_exists_small_unit_mass_block e h hε
  · intro h
    rintro ⟨L, hL, hbound⟩
    obtain ⟨b, hb, hnorm⟩ := h (L / 2) (by positivity)
    have hlow := hbound b
    rw [hb, mul_one] at hlow
    linarith

end SurveyStatements.P1
