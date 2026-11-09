import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Problem 5: primariness of Lp(L1)

Source: `source/problems/P5-primariness-Lp_L1.tex`, Theorem `p3:thm:main`.
The source works over the reals and explicitly states the complex extension;
`RCLike` covers both fields. Both conclusions of the main theorem are retained.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

universe u v

namespace SurveyStatements.P5

/-- Lebesgue measure on the unit interval. Using a restricted measure on `ℝ`
gives the usual interval Lp spaces, modulo almost-everywhere equality. -/
def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The genuine Bochner space `Lp([0,1]; L1([0,1]; 𝕜))`.
The outer exponent is an extended nonnegative real; the main result explicitly
excludes both `p ≤ 1` and `p = ∞`. -/
abbrev MixedNorm (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) :=
  Lp (Lp 𝕜 1 unitIntervalMeasure) p unitIntervalMeasure

variable (𝕜 : Type u) [RCLike 𝕜]
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One norm bound, chosen before the operator, works in the primary
factorization dichotomy. Both factors may depend on the operator. -/
def HasUniformPrimaryFactorization : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ T : E →L[𝕜] E,
    ∃ A B : E →L[𝕜] E, ‖A‖ * ‖B‖ ≤ K ∧
      ((A.comp T).comp B = ContinuousLinearMap.id 𝕜 E ∨
       (A.comp (ContinuousLinearMap.id 𝕜 E - T)).comp B =
         ContinuousLinearMap.id 𝕜 E)

/-- Primariness: the range of every bounded projection, or the complementary
range, is isomorphic to the whole space by a continuous linear equivalence.
For a projection these are precisely the two complemented summands. -/
def IsPrimary : Prop :=
  ∀ P : E →L[𝕜] E, P.comp P = P →
    Nonempty (E ≃L[𝕜] LinearMap.range P.toLinearMap) ∨
    Nonempty (E ≃L[𝕜]
      LinearMap.range (ContinuousLinearMap.id 𝕜 E - P).toLinearMap)

end SurveyStatements.P5

