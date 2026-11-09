import SurveyStatements.P5Support.LpHaarBlockReaderDecay
import SurveyStatements.P5OperatorReductionCandidateSplits

/-! A fresh normalized block reader acting on a fixed actual Lp vector
has vanishing full-cube moments, uniformly in the selected signs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]

theorem refined_blockReader_second_moment_tendsto_zero (p : BanachExponent)
    (P : LpHaarFiniteParent) (y : IntervalLp 𝕜 p) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖lpHaarSignedBlockReader 𝕜 p n (lpHaarRefineAt P.level P.atoms n) θ y‖ ^ 2))
      atTop (𝓝 0) := by
  have hmass : ∀ᶠ n in atTop, (volume.restrict (Set.Icc (0 : ℝ) 1)).real P.set ≤
      ((lpHaarRefineAt P.level P.atoms n).card : ℝ) * intervalLpDyadicRadius n := by
    filter_upwards [eventually_ge_atTop P.level] with n hn
    rw [lpHaarRefineAt_mass P.level P.atoms n hn]
    change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent P.level P.atoms) ≤ _
    rw [lpHaarBlockParent_real_measure]
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (mean_nonneg (fun _ => sq_nonneg _)))
  · intro b hb
    have he : 0 < Real.sqrt (b / 2) := Real.sqrt_pos.mpr (half_pos hb)
    filter_upwards [lpHaarSignedBlockReader_uniform_small 𝕜 p
      (lpHaarRefineAt P.level P.atoms) P.mass_pos he hmass y] with n hn
    have hs : mean (fun θ : Fin (2 ^ n) → Bool =>
        ‖lpHaarSignedBlockReader 𝕜 p n (lpHaarRefineAt P.level P.atoms n) θ y‖ ^ 2) ≤
        (Real.sqrt (b / 2)) ^ 2 := by
      apply (mean_mono (fun θ =>
        pow_le_pow_left₀ (norm_nonneg _) (hn θ).le 2)).trans_eq (mean_const _)
    rw [Real.sq_sqrt (half_pos hb).le] at hs
    exact hs.trans_lt (by linarith)

theorem candidate_blockReader_second_moment_tendsto_zero (p : BanachExponent)
    (P : LpHaarFiniteParent) (y : IntervalLp 𝕜 p) :
    Tendsto (fun n => mean (fun θ : Fin (2 ^ n) → Bool =>
      ‖(candidateRefinedSplit P n θ).reader 𝕜 p y‖ ^ 2)) atTop (𝓝 0) := by
  apply (refined_blockReader_second_moment_tendsto_zero p P y).congr'
  filter_upwards [eventually_ge_atTop P.level] with n hn
  apply congrArg mean
  funext θ
  rw [candidateRefinedSplit_eq P n hn θ]
  rfl

end SurveyStatements.P5OperatorReduction
