import PEMS.FiniteAlmostDisjointSequence
import PEMS.AlmostDisjointFactorization
import PEMS.FactorizationSupContractions
import PEMS.MainStatements

/-! Theorem 1.4 for actual real and complex L1 spaces over finite measures.
The non-weakly-compact case uses the constructed sequences of Lemma 5.4;
the zero weak-essential-norm case uses the adjoined zero in the supremum.
The abstract AL-space representation and arbitrary-measure transfer are
separate results. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem weakEssentialNorm_eq_factorizationSup_real_finite
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = factorizationSup (EllOne ℝ) T := by
  letI : Nontrivial (EllOne ℝ) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : EllOne ℝ => x 0) h
    simpa using hc⟩⟩
  apply le_antisymm _ (factorizationSup_ellOne_le_weakEssentialNorm T)
  by_cases hT : IsWeaklyCompactOperator T
  · rw [hT.weakEssentialNorm_eq_zero]
    exact factorizationSup_nonneg T
  · obtain ⟨u, g, hdu, hdg, hu, herr, hnorm⟩ := lemma_5_4_real_finite T hT
    exact (weakEssentialNorm_eq_factorizationSup_of_almost_disjoint
      T u g hdu hdg hu herr hnorm).le

theorem weakEssentialNorm_eq_factorizationSup_complex_finite
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm T = factorizationSup (EllOne ℂ) T := by
  letI : Nontrivial (EllOne ℂ) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : EllOne ℂ => x 0) h
    simpa using hc⟩⟩
  apply le_antisymm _ (factorizationSup_ellOne_le_weakEssentialNorm T)
  by_cases hT : IsWeaklyCompactOperator T
  · rw [hT.weakEssentialNorm_eq_zero]
    exact factorizationSup_nonneg T
  · obtain ⟨u, g, hdu, hdg, hu, herr, hnorm⟩ := lemma_5_4_complex_finite T hT
    exact (weakEssentialNorm_eq_factorizationSup_of_almost_disjoint
      T u g hdu hdg hu herr hnorm).le

theorem theorem_1_4_real_finite (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    Theorem_1_4 (LOne ℝ μ) (LOne ℝ ν) T := by
  intro _ _
  exact weakEssentialNorm_eq_factorizationSup_real_finite T

theorem theorem_1_4_complex_finite (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    Theorem_1_4 (LOne ℂ μ) (LOne ℂ ν) T := by
  intro _ _
  exact weakEssentialNorm_eq_factorizationSup_complex_finite T

end PEMS
