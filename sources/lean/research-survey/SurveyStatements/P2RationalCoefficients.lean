import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Countable dense finite complex coefficient codes for the compact corrections. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P2

def rationalComplex (q : ℚ × ℚ) : ℂ :=
  Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ))

theorem denseRange_rationalComplex : DenseRange rationalComplex := by
  have hrat : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
  exact Complex.equivRealProdCLM.symm.surjective.denseRange.comp (hrat.prodMap hrat)
    Complex.equivRealProdCLM.symm.continuous

theorem denseRange_rationalComplexFamily (ι : Type*) :
    DenseRange (fun a : ι → ℚ × ℚ => fun j => rationalComplex (a j)) :=
  DenseRange.piMap (fun _ => denseRange_rationalComplex)

/-- A genuinely countable collection encoding every rational complex finite row. -/
abbrev RationalFiniteCoefficients := Σ F : Finset ℕ, F → ℚ × ℚ

example : Countable RationalFiniteCoefficients := inferInstance

/-- Continuity extends the finite-row norm estimate to all complex coefficients. -/
theorem finite_row_bound_of_rational {ι Z : Type*} [Fintype ι]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] (x : ι → Z) (C : ℝ)
    (hrat : ∀ a : ι → ℚ × ℚ,
      ‖∑ j, rationalComplex (a j) • x j‖ ≤ C * ‖fun j => rationalComplex (a j)‖)
    (a : ι → ℂ) : ‖∑ j, a j • x j‖ ≤ C * ‖a‖ := by
  refine (denseRange_rationalComplexFamily ι).induction_on
    (p := fun b : ι → ℂ => ‖∑ j, b j • x j‖ ≤ C * ‖b‖) a ?_ hrat
  apply isClosed_le
  · exact (continuous_finset_sum _ (fun j _ => (continuous_apply j).smul continuous_const)).norm
  · exact continuous_const.mul continuous_norm

end SurveyStatements.P2
