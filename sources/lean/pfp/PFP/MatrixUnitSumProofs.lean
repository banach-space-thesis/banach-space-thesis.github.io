import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixUnitSumNorms

/-! Both exact operator-norm formulas of Lemma 5.6, with the arbitrary
unimodular coefficients and the printed conjugate exponent. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem lemma_5_6 : Lemma_5_6 𝕜 := by
  intro p hp hfin N I J _hI hJ ε δ hε hδ i j
  have hpReal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
  exact ⟨norm_matrixUnit_column_sum p (zero_lt_one.trans hpReal) I ε hε j,
    norm_matrixUnit_row_sum p hpReal J hJ δ hδ i⟩

end PFP
