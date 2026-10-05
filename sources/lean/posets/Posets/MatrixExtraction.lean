import Posets.ScalarExtraction
import PosetsCommon.CZeroSum

/-! The concrete coefficient matrix used to construct θ. Row summability,
vanishing columns and the incidence-algebra operator norm still require the
common-subspace estimates of Section 6; they are not assumed here. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open ThesisCommon
namespace Posets
variable {𝕜 P : Type*} [RCLike 𝕜] [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t}

def blockScalarMatrix (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s t : P) : 𝕜 :=
  if hts : t ≤ s then fewOperatorCoefficient h hts (operatorBlock 𝕜 X X T s t) else 0

theorem blockScalarMatrix_add (h : FewOperators 𝕜 X ι)
    (T U : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    blockScalarMatrix h (T + U) = blockScalarMatrix h T + blockScalarMatrix h U := by
  funext s t
  by_cases hts : t ≤ s
  · simp [blockScalarMatrix, hts, operatorBlock, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp]
  · simp [blockScalarMatrix, hts]

theorem blockScalarMatrix_smul (h : FewOperators 𝕜 X ι)
    (a : 𝕜) (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    blockScalarMatrix h (a • T) = a • blockScalarMatrix h T := by
  funext s t
  by_cases hts : t ≤ s
  · simp [blockScalarMatrix, hts, operatorBlock, ContinuousLinearMap.smul_comp]
  · simp [blockScalarMatrix, hts]

theorem blockScalarMatrix_zero_off_order (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) {s t : P} (hts : ¬ t ≤ s) :
    blockScalarMatrix h T s t = 0 := by simp [blockScalarMatrix, hts]

theorem blockScalarMatrix_remainder (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s t : P) :
    HasSeparableRange 𝕜 (X t) (X s)
      (operatorBlock 𝕜 X X T s t - blockScalarMatrix h T s t • ι t s) := by
  by_cases hts : t ≤ s
  · simpa [blockScalarMatrix, hts, fewOperatorCoefficient, scalarBetweenL] using
      scalarBetween_remainder (fewOperators_scalarDecompositions h hts) (operatorBlock 𝕜 X X T s t)
  · simpa [blockScalarMatrix, hts] using
      h.2.2.2.2.2 t s hts (operatorBlock 𝕜 X X T s t)

theorem blockScalarMatrix_entry_zero_iff (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s t : P) :
    blockScalarMatrix h T s t = 0 ↔
      HasSeparableRange 𝕜 (X t) (X s) (operatorBlock 𝕜 X X T s t) := by
  by_cases hts : t ≤ s
  · simpa [blockScalarMatrix, hts, fewOperatorCoefficient, scalarBetweenL] using
      scalarBetween_eq_zero_iff (h.1 t) (h.2.1 t s hts)
        (fewOperators_scalarDecompositions h hts) (operatorBlock 𝕜 X X T s t)
  · simp only [blockScalarMatrix, dif_neg hts, true_iff]
    exact h.2.2.2.2.2 t s hts (operatorBlock 𝕜 X X T s t)

theorem blockScalarMatrix_entry_norm_le (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) (s t : P) :
    ‖blockScalarMatrix h T s t‖ ≤ ‖operatorBlock 𝕜 X X T s t‖ := by
  by_cases hts : t ≤ s
  · simpa [blockScalarMatrix, hts, fewOperatorCoefficient, scalarBetweenL] using
      scalarBetween_norm_le (h.1 t) (h.2.1 t s hts)
        (fewOperators_scalarDecompositions h hts) (operatorBlock 𝕜 X X T s t)
  · simp [blockScalarMatrix, hts]

theorem blockScalarMatrix_zero_iff_blocks (h : FewOperators 𝕜 X ι)
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 X) :
    blockScalarMatrix h T = 0 ↔
      ∀ s t, HasSeparableRange 𝕜 (X t) (X s) (operatorBlock 𝕜 X X T s t) := by
  simp only [funext_iff, Pi.zero_apply, blockScalarMatrix_entry_zero_iff]

end Posets
