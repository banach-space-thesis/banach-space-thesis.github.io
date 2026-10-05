import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixBlockKilling

/-! The full finite-dimensional block projection lemma on the genuine
finite matrix operator spaces. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem lemma_5_9 : Lemma_5_9 𝕜 := by
  intro p hp hfin k d hk hd ε hε _
  have hpReal : 1 < p.val.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
  exact exists_matrixBlock_small_on_subspace p hpReal hfin k d hk hd hε

end PFP
