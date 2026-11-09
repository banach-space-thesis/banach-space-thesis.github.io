import SurveyStatements.P1SuppressionWitnesses

/-! The quantitative contradiction from two matched finite witnesses.
The common selected set supplies positive real mass, and support
stabilization bounds every remaining evaluation by one. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem matched_unitSuppressionWitness_cross_bound
    {e : ℕ → X} {A : Finset ℂ} (hA : ∀ α ∈ A, ‖α‖ = 1)
    (w v : UnitSuppressionWitness e A) (L M : Set ℕ)
    (hvM : (v.coefficients.support : Set ℕ) ⊆ M)
    (hselected : w.selected ⊆ v.selected)
    (hinter : L ∩ M = (w.selected : Set ℕ))
    (hcoeff : v.phaseCoeff = w.phaseCoeff) (hvalue : v.phaseValue = w.phaseValue)
    (hoff : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ M \ L →
      ∑ i ∈ S, ‖w.functional (e i)‖ ≤ 1) :
    (1 / 2 : ℝ) * w.mass - 1 ≤
      ‖Finsupp.linearCombination ℂ e v.coefficients‖ := by
  let ζ := (w.phaseCoeff * w.phaseValue)⁻¹
  have hζ : ‖ζ‖ = 1 := by
    simp only [ζ, norm_inv, norm_mul, hA _ w.phaseCoeff_mem,
      hA _ w.phaseValue_mem, one_mul, inv_one]
  let C := w.selected
  let R := v.coefficients.support \ C
  have hC : C ⊆ v.coefficients.support := hselected.trans v.selected_subset
  have hR : (R : Set ℕ) ⊆ M \ L := by
    intro i hi
    obtain ⟨hia, hiC⟩ := Finset.mem_sdiff.mp hi
    refine ⟨hvM hia, ?_⟩
    intro hiL
    have him : i ∈ L ∩ M := ⟨hiL, hvM hia⟩
    rw [hinter] at him
    exact hiC him
  have hpos : (1 / 2 : ℝ) * w.mass ≤
      (ζ * ∑ i ∈ C, v.coefficients i * w.functional (e i)).re := by
    change (1 / 2 : ℝ) * (∑ i ∈ C, ‖w.functional (e i)‖) ≤ _
    rw [Finset.mul_sum, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := matched_phase_sector_realPart_bound (v.coefficients i)
      (w.functional (e i)) w.phaseCoeff w.phaseValue
      (v.coefficients_unit i (hC hi)) (hA _ w.phaseCoeff_mem) (hA _ w.phaseValue_mem)
      (by simpa only [hcoeff] using v.coefficient_near i (hselected hi))
      (w.functional_near i hi)
    simpa only [ζ, mul_assoc] using h
  have hres : ‖ζ * ∑ i ∈ R, v.coefficients i * w.functional (e i)‖ ≤ 1 := by
    calc
      _ = ‖∑ i ∈ R, v.coefficients i * w.functional (e i)‖ := by rw [norm_mul, hζ, one_mul]
      _ ≤ ∑ i ∈ R, ‖v.coefficients i * w.functional (e i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ R, ‖w.functional (e i)‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, v.coefficients_unit i (Finset.mem_sdiff.mp hi).1, one_mul]
      _ ≤ 1 := hoff R hR
  have hresre : -1 ≤ (ζ * ∑ i ∈ R, v.coefficients i * w.functional (e i)).re := by
    have h := neg_le_abs (ζ * ∑ i ∈ R, v.coefficients i * w.functional (e i)).re
    have habs := Complex.abs_re_le_norm (ζ * ∑ i ∈ R, v.coefficients i * w.functional (e i))
    linarith
  have hsplit :
      (∑ i ∈ C, v.coefficients i * w.functional (e i)) +
        (∑ i ∈ R, v.coefficients i * w.functional (e i)) =
      w.functional (Finsupp.linearCombination ℂ e v.coefficients) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    simpa only [add_comm] using
      (Finset.sum_sdiff hC (f := fun i => v.coefficients i * w.functional (e i)))
  have htotal : (1 / 2 : ℝ) * w.mass - 1 ≤
      (ζ * w.functional (Finsupp.linearCombination ℂ e v.coefficients)).re := by
    rw [← hsplit, mul_add, Complex.add_re]
    linarith
  refine htotal.trans (((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans ?_)
  rw [norm_mul, hζ, one_mul]
  calc
    _ ≤ ‖w.functional‖ * ‖Finsupp.linearCombination ℂ e v.coefficients‖ :=
      w.functional.le_opNorm _
    _ ≤ 1 * ‖Finsupp.linearCombination ℂ e v.coefficients‖ :=
      mul_le_mul_of_nonneg_right w.functional_bound
        (norm_nonneg (Finsupp.linearCombination ℂ e v.coefficients))
    _ = _ := one_mul _

theorem matched_unitSuppressionWitness_contradiction
    {e : ℕ → X} {A : Finset ℂ} (hA : ∀ α ∈ A, ‖α‖ = 1)
    (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (w v : UnitSuppressionWitness e A) (L M : Set ℕ)
    (hvM : (v.coefficients.support : Set ℕ) ⊆ M)
    (hselected : w.selected ⊆ v.selected)
    (hinter : L ∩ M = (w.selected : Set ℕ))
    (hcoeff : v.phaseCoeff = w.phaseCoeff) (hvalue : v.phaseValue = w.phaseValue)
    (hmass : v.mass - 1 ≤ w.mass)
    (hoff : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ M \ L →
      ∑ i ∈ S, ‖w.functional (e i)‖ ≤ 1) : False := by
  have hcross := matched_unitSuppressionWitness_cross_bound hA w v L M hvM
    hselected hinter hcoeff hvalue hoff
  have hlarge : 20 * ‖Finsupp.linearCombination ℂ e v.coefficients‖ < v.mass := v.mass_large
  have hfive := v.mass_gt_five he hp
  linarith

end SurveyStatements.P1
