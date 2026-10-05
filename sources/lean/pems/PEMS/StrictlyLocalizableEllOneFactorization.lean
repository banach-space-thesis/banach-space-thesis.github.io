import PEMS.FiniteMeasureWitnessReduction
import PEMS.FiniteEllOneFactorization
import PEMS.DisjointOutputWitnessWeis

/-! The sharp ℓ¹ factorization formula on actual L1 spaces with strictly
localizable input and arbitrary output measure. A countable output-cut witness
is transported to finite measures; the maps contract both factorization and
weak essential norms. The zero case is included. -/
noncomputable section
open MeasureTheory ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = factorizationSup (EllOne ℝ) T := by
  letI : Nontrivial (EllOne ℝ) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : EllOne ℝ => x 0) h
    simpa using hc⟩⟩
  apply le_antisymm _ (factorizationSup_ellOne_le_weakEssentialNorm T)
  by_cases hT : IsWeaklyCompactOperator T
  · rw [hT.weakEssentialNorm_eq_zero]
    exact factorizationSup_nonneg T
  · obtain ⟨f, A, hA, c, hf, _, hd, hw, hc⟩ :=
      exists_real_disjointOutputWitness_weakEssentialNorm hμ T hT
    obtain ⟨ρ, hρ, η, hη, R, hloc, _, hfac⟩ :=
      exists_real_finite_measure_witness_reduction T f (fun n => (hf n).le) A hA hd hc
    letI := hρ
    letI := hη
    calc
      weakEssentialNorm T ≤ c := hw
      _ ≤ localizedWeakNoncompactness R := hloc
      _ = weakEssentialNorm R := (weakEssentialNorm_eq_localized_real_finite R).symm
      _ = factorizationSup (EllOne ℝ) R := weakEssentialNorm_eq_factorizationSup_real_finite R
      _ ≤ factorizationSup (EllOne ℝ) T := hfac

theorem theorem_1_4_real_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    Theorem_1_4 (LOne ℝ μ) (LOne ℝ ν) T := by
  intro _ _
  exact weakEssentialNorm_eq_factorizationSup_real_strictlyLocalizable hμ T

theorem weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    weakEssentialNorm T = factorizationSup (EllOne ℂ) T := by
  letI : Nontrivial (EllOne ℂ) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : EllOne ℂ => x 0) h
    simpa using hc⟩⟩
  apply le_antisymm _ (factorizationSup_ellOne_le_weakEssentialNorm T)
  by_cases hT : IsWeaklyCompactOperator T
  · rw [hT.weakEssentialNorm_eq_zero]
    exact factorizationSup_nonneg T
  · obtain ⟨f, A, hA, c, hf, _, hd, hw, hc⟩ :=
      exists_complex_disjointOutputWitness_weakEssentialNorm hμ T hT
    obtain ⟨ρ, hρ, η, hη, R, hloc, _, hfac⟩ :=
      exists_complex_finite_measure_witness_reduction T f (fun n => (hf n).le) A hA hd hc
    letI := hρ
    letI := hη
    calc
      weakEssentialNorm T ≤ c := hw
      _ ≤ localizedWeakNoncompactness R := hloc
      _ = weakEssentialNorm R := (weakEssentialNorm_eq_localized_complex_finite R).symm
      _ = factorizationSup (EllOne ℂ) R := weakEssentialNorm_eq_factorizationSup_complex_finite R
      _ ≤ factorizationSup (EllOne ℂ) T := hfac

theorem theorem_1_4_complex_strictlyLocalizable
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    Theorem_1_4 (LOne ℂ μ) (LOne ℂ ν) T := by
  intro _ _
  exact weakEssentialNorm_eq_factorizationSup_complex_strictlyLocalizable hμ T

end PEMS
