import CKEUPFP.ScalarLpCounting
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Real.Cardinality

/-! Separability of the actual finite-exponent scalar spaces used in the
mixed continuous-function corollary. -/

noncomputable section

open scoped ENNReal

namespace CKEUPFP

theorem unitInterval_uncountable : Uncountable UnitInterval := by
  rw [← not_countable_iff]
  intro hcount
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1))
    (Cardinal.Real.Icc_countable_iff.mp hcount)

variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalarEllp_separableSpace (p : FiniteBanachExponent) :
    TopologicalSpace.SeparableSpace (ScalarEllp 𝕜 p) := by
  letI : Fact (p.val ≠ ∞) := ⟨p.property.2.ne⟩
  letI : SecondCountableTopology (ScalarEllp 𝕜 p) :=
    (scalarLpCountingIsometry (𝕜 := 𝕜) p).isometry.isEmbedding.secondCountableTopology
  infer_instance

theorem intervalLp_separableSpace (p : FiniteBanachExponent) :
    TopologicalSpace.SeparableSpace (IntervalLp 𝕜 p) := by
  letI : Fact (p.val ≠ ∞) := ⟨p.property.2.ne⟩
  infer_instance

end CKEUPFP
