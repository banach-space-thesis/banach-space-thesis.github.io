import PEMS.RealWeisBestApproximation
import PEMS.CountablyGeneratedWeisFormula

/-! Real best weakly compact approximation on arbitrary finite countably
generated measure spaces, transported through the proved Cantor models.
No point-map isomorphism or nonzero-measure hypothesis is needed. -/
noncomputable section
open MeasureTheory MeasurableSpace ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [CountablyGenerated X] [CountablyGenerated Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem weaklyCompact_abs_iff_real_countablyGenerated
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    IsWeaklyCompactOperator |T| ↔ IsWeaklyCompactOperator T := by
  rw [← weakEssentialNorm_eq_zero_iff |T|, ← weakEssentialNorm_eq_zero_iff T,
    weakEssentialNorm_abs_real_countablyGenerated]

theorem exists_real_countablyGenerated_weaklyCompact_bestApproximation
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ W : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator W ∧
      ‖T - W‖ = weakEssentialNorm T := by
  let μC : Measure (ℕ → Bool) := μ.map (mapNatBool X)
  let νC : Measure (ℕ → Bool) := ν.map (mapNatBool Y)
  let Φ : MeasureAlgebraIso μ μC := cantorMeasureAlgebraIso X μ
  let Ψ : MeasureAlgebraIso ν νC := cantorMeasureAlgebraIso Y ν
  let e := measureAlgebraOperatorEquiv Φ Ψ
  obtain ⟨W, hW, hnorm⟩ := exists_real_standard_weaklyCompact_bestApproximation (e T)
  have hweak : IsWeaklyCompactOperator (e.symm W) := by
    apply (weaklyCompact_operatorTransport_iff Φ.lOneEquiv Ψ.lOneEquiv (e.symm W)).mp
    change IsWeaklyCompactOperator (e (e.symm W))
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hW
  refine ⟨e.symm W, hweak, ?_⟩
  calc
    ‖T - e.symm W‖ = ‖e (T - e.symm W)‖ := (e.norm_map _).symm
    _ = ‖e T - W‖ := by rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    _ = weakEssentialNorm (e T) := hnorm
    _ = weakEssentialNorm T :=
      weakEssentialNorm_operatorTransport Φ.lOneEquiv Ψ.lOneEquiv T

end PEMS
