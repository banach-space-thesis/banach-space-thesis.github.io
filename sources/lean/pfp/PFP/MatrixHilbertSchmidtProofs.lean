import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixHilbertSchmidtComparison

/-! Exact Lemma 5.8, including the strict deviation bound and both printed
dimension exponents, on the actual real or complex lp operator spaces. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem lemma_5_8 : Lemma_5_8 𝕜 := by
  intro p hp hfin
  have hpReal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
  exact ⟨matrixExponentDeviation_lt_half p hpReal,
    fun N hN A => matrixHilbertSchmidtNorm_le_dimension_mul_norm p hfin hN A,
    fun N hN A => norm_le_dimension_mul_matrixHilbertSchmidtNorm p hfin hN A⟩

end PFP
