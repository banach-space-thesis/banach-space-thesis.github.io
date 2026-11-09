import SurveyStatements.P5PiecewiseOperatorLift

/-! Bounds for finite disjoint families with any common nonnegative norm bound. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_disjoint_operator_indicators_bound {ι : Type*}
    (F : Finset ι) (S : ι → Set ℝ) (L : ι → E →L[𝕜] E)
    {C : ℝ} (hC : 0 ≤ C)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hL : ∀ i ∈ F, ‖L i‖ ≤ C) (x : ℝ) (f : ℝ → E) :
    ‖∑ i ∈ F, (S i).indicator (fun x => L i (f x)) x‖ ≤ C * ‖f x‖ := by
  by_cases hactive : ∃ i ∈ F, x ∈ S i
  · obtain ⟨i, hi, hxi⟩ := hactive
    have hsum : (∑ j ∈ F, (S j).indicator (fun x => L j (f x)) x) =
        (S i).indicator (fun x => L i (f x)) x := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hxj : x ∉ S j := (hdisjoint i hi j hj hji.symm).notMem_of_mem_left hxi
        simp [hxj]
      · intro hn
        exact (hn hi).elim
    rw [hsum, Set.indicator_of_mem hxi]
    exact ((L i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hL i hi) (norm_nonneg _))
  · have hzero : (∑ i ∈ F, (S i).indicator (fun x => L i (f x)) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hxi : x ∉ S i := fun hx => hactive ⟨i, hi, hx⟩
      simp [hxi]
    rw [hzero, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

theorem norm_piecewiseOperatorLift_bound {ι : Type*}
    (F : Finset ι) (S : ι → Set ℝ) (hS : ∀ i, MeasurableSet (S i))
    (L : ι → E →L[𝕜] E) {C : ℝ} (hC : 0 ≤ C)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hL : ∀ i ∈ F, ‖L i‖ ≤ C) :
    ‖piecewiseOperatorLift (p := p) F S hS L‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [piecewiseOperatorLift_ae F S hS L f] with x hx
  rw [hx]
  exact norm_disjoint_operator_indicators_bound F S L hC hdisjoint hL x f

end SurveyStatements.P5
