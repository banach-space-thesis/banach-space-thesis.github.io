import PL1.DiscreteInterpolation

/-! # Extended-valued discrete interpolation norm

The ENNReal quantity retains infinity on nonsummable inputs. Its finite
domain is exactly the original intrinsic space of functions.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.DiscreteInterpolation
open Noise Walsh IntrinsicGraph ResolventEstimates

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

def extendedNorm (f : Lp K 1 haar) : ℝ≥0∞ :=
  ENNReal.ofReal ‖f‖ + ∑' n, ENNReal.ofReal (term K rates f n)

theorem tsum_term_ne_top_iff (f : Lp K 1 haar) :
    (∑' n, ENNReal.ofReal (term K rates f n)) ≠ ⊤ ↔ Summable (term K rates f) := by
  constructor
  · intro h
    have hs := ENNReal.summable_toReal h
    simpa only [ENNReal.toReal_ofReal (term_nonneg K rates f _)] using hs
  · exact Summable.tsum_ofReal_ne_top

theorem extendedNorm_ne_top_iff (f : Lp K 1 haar) :
    extendedNorm K rates f ≠ ⊤ ↔ f ∈ (evalZero (dyadicSystem K rates).analysis).range := by
  rw [extendedNorm, ENNReal.add_ne_top, and_iff_right ENNReal.ofReal_ne_top,
    tsum_term_ne_top_iff, mem_range_evalZero_iff]

theorem extendedNorm_eq_of_summable (f : Lp K 1 haar) (hf : Summable (term K rates f)) :
    extendedNorm K rates f = ENNReal.ofReal (normValue K rates f) := by
  rw [extendedNorm, normValue, ENNReal.ofReal_add (norm_nonneg _)
    (tsum_nonneg (term_nonneg K rates f)), ENNReal.ofReal_tsum_of_nonneg (term_nonneg K rates f) hf]

theorem extendedNorm_eval_eq (x : (dyadicSystem K rates).IntrinsicSpace) :
    extendedNorm K rates (evalZero (dyadicSystem K rates).analysis x) =
      ENNReal.ofReal (normValue K rates (evalZero (dyadicSystem K rates).analysis x)) :=
  extendedNorm_eq_of_summable K rates _ (summable_term_eval K rates x)

end PL1.DiscreteInterpolation
