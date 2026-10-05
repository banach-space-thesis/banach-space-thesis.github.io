import PEMS.RealWeisFormula
import PEMS.MeasureAlgebraNoncompactness
import PEMS.MeasureAlgebraTransport
import ThesisCommon.Analysis.StandardMeasureRepresentation

/-! The real Weis norm identity on arbitrary finite countably generated
measure spaces. Explicit Cantor coding supplies compact standard models;
the exact localized functional and every actual signed kernel truncation
are transported through their measure-algebra isometries.

These are norm-formulation results. Identifying the truncation infimum
with the particular essential-supremum expression displayed in source
Theorem 4.4 remains a separate source-correspondence step. -/
noncomputable section
open MeasureTheory MeasurableSpace Set ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [CountablyGenerated X] [CountablyGenerated Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The exact localized functional equals distance to the actual weakly
compact operator ideal. Null measures and empty original spaces are included. -/
theorem weakEssentialNorm_eq_localized_real_countablyGenerated
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    weakEssentialNorm T = localizedWeakNoncompactness T := by
  let μC : Measure (ℕ → Bool) := μ.map (mapNatBool X)
  let νC : Measure (ℕ → Bool) := ν.map (mapNatBool Y)
  let Φ : MeasureAlgebraIso μ μC := cantorMeasureAlgebraIso X μ
  let Ψ : MeasureAlgebraIso ν νC := cantorMeasureAlgebraIso Y ν
  exact (weakEssentialNorm_eq_localized_measureAlgebraTransport_iff Φ Ψ T).mp
    (weakEssentialNorm_eq_localized_real_standard (measureAlgebraOperatorEquiv Φ Ψ T))

/-- The norm formula for every genuine singular-plus-integral decomposition
and every supplied real integral kernel. The explicit kernel part of Lemma
4.3 preserves all large-value truncations, with the source `≥` convention. -/
theorem real_countablyGenerated_weis_norm_formula
    {k : X × Y → ℝ} (S K : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm (S + K) = localizedWeakNoncompactness (S + K) ∧
    weakEssentialNorm (S + K) =
      sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  refine ⟨weakEssentialNorm_eq_localized_real_countablyGenerated (S + K), ?_⟩
  let μC : Measure (ℕ → Bool) := μ.map (mapNatBool X)
  let νC : Measure (ℕ → Bool) := ν.map (mapNatBool Y)
  let Φ : MeasureAlgebraIso μ μC := cantorMeasureAlgebraIso X μ
  let Ψ : MeasureAlgebraIso ν νC := cantorMeasureAlgebraIso Y ν
  let e := measureAlgebraOperatorEquiv Φ Ψ
  obtain ⟨h, hh, htr⟩ := hk.exists_measureAlgebra_transport Φ Ψ
  have hSC : IsSingularOperator (e S) :=
    (isSingularOperator_measureAlgebraTransport_iff Φ Ψ S).mpr hS
  have hhC : IsIntegralKernel h (e K) := hh
  have hnorm : ∀ n : ℕ, ‖e S + hhC.truncatedOperator n‖ = ‖S + hk.truncatedOperator n‖ := by
    intro n
    rw [show hhC.truncatedOperator n = e (hk.truncatedOperator n) from htr n, ← map_add]
    exact e.norm_map _
  have hw : weakEssentialNorm (e S + e K) = weakEssentialNorm (S + K) := by
    rw [← map_add]
    exact weakEssentialNorm_operatorTransport Φ.lOneEquiv Ψ.lOneEquiv (S + K)
  have hformula := (real_standard_weis_norm_formula (e S) (e K) hSC hhC).2
  rw [hw] at hformula
  simpa only [hnorm] using hformula

theorem real_countablyGenerated_weis_norm_formula_of_decomposition
    {k : X × Y → ℝ} (T S K : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hT : T = S + K) (hS : IsSingularOperator S) (hk : IsIntegralKernel k K) :
    weakEssentialNorm T = localizedWeakNoncompactness T ∧
    weakEssentialNorm T = sInf (Set.range (fun n : ℕ => ‖S + hk.truncatedOperator n‖)) := by
  subst T
  exact real_countablyGenerated_weis_norm_formula S K hS hk

theorem weakEssentialNorm_abs_real_countablyGenerated
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : weakEssentialNorm |T| = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_localized_real_countablyGenerated, localizedWeakNoncompactness_abs,
    weakEssentialNorm_eq_localized_real_countablyGenerated]

end PEMS
