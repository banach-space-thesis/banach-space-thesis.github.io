import SurveyStatements.P5OperatorReductionConcreteEntrySlices
import SurveyStatements.P5OperatorReductionOneSidedMoments
import SurveyStatements.P5OperatorReductionBackwardMoments

/-! Every actual off-diagonal entry with exactly one fresh block has
vanishing signed second moment, on its genuine fixed physical parent. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem candidate_functional_second_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (P : LpHaarFiniteParent)
    (φ : IntervalLp 𝕜 p →L[𝕜] 𝕜) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖φ ((candidateRefinedSplit P n θ).vector 𝕜 p)‖ ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ‖φ‖ ^ 2 * intervalLpDyadicRadius n ^
      (1 / p.val.toReal)) atTop (𝓝 0) := by
    simpa using (lpHaarDyadic_norm_radius_tendsto_zero p hp).const_mul (‖φ‖ ^ 2)
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall (fun _ => hε.trans_le (mean_nonneg (fun _ => sq_nonneg _)))
  · intro ε hε
    filter_upwards [eventually_ge_atTop P.level, (tendsto_order.mp ht).2 ε hε] with n hn hs
    apply lt_of_le_of_lt _ hs
    convert functional_signedBlock_second_moment_le p hp φ n
      (lpHaarRefineAt P.level P.atoms n) using 1
    apply congrArg mean
    funext θ
    rw [candidateRefinedSplit_eq P n hn θ]
    rfl

theorem concrete_entry_inner_source_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Os : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖concreteMixedEntry p T Ot It Os (candidateRefinedSplit P n θ)‖ ^ 2))
      atTop (𝓝 0) := by
  simpa only [concreteMixedEntry_innerInput] using
    candidate_functional_second_moment_tendsto_zero concreteInnerExponent (by simp)
      P (concreteInnerInputFunctional p T Ot It Os)

theorem concrete_entry_inner_target_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot Os Is : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖concreteMixedEntry p T Ot (candidateRefinedSplit P n θ) Os Is‖ ^ 2))
      atTop (𝓝 0) := by
  simpa only [concreteMixedEntry_innerOutput] using
    candidate_blockReader_second_moment_tendsto_zero concreteInnerExponent
      P (concreteInnerOutputVector p T Ot Os Is)

theorem concrete_entry_outer_source_moment_tendsto_zero (p : BanachExponent)
    (hp : p.val ≠ ∞) (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (Ot It Is : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖concreteMixedEntry p T Ot It (candidateRefinedSplit P n θ) Is‖ ^ 2))
      atTop (𝓝 0) := by
  simpa only [concreteMixedEntry_outerInput] using
    candidate_functional_second_moment_tendsto_zero p hp
      P (concreteOuterInputFunctional p T Ot It Is)

theorem concrete_entry_outer_target_moment_tendsto_zero (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (It Os Is : LpHaarFiniteSplit) (P : LpHaarFiniteParent) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖concreteMixedEntry p T (candidateRefinedSplit P n θ) It Os Is‖ ^ 2))
      atTop (𝓝 0) := by
  simpa only [concreteMixedEntry_outerOutput] using
    candidate_blockReader_second_moment_tendsto_zero p P (concreteOuterOutputVector p T It Os Is)

end SurveyStatements.P5OperatorReduction
