import PEMS.ExtremalDisjointResidual
import ThesisCommon.Analysis.L1UniformIntegrableCutSequence

/-! Extremal cutoff sequences have unit asymptotic input norm. These estimates
justify the normalization step in source Lemma 5.4. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem eventually_cutOperatorNorm_lt_alphaTheta_univ_add
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (A : ℕ → Set Y)
    (hA : ∀ n, MeasurableSet (A n)) (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, cutOperatorNorm T (A n) < alphaTheta T univ + ε := by
  obtain ⟨r, ⟨δ, hδ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (s := {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T univ δ})
    ⟨_, 1, zero_lt_one, rfl⟩
    (show alphaTheta T univ < alphaTheta T univ + ε by linarith)
  filter_upwards [hmass.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))] with n hn
  apply lt_of_le_of_lt _ hr
  simpa only [compl_univ, empty_union] using
    cutOperatorNorm_le_smallSetSup T univ MeasurableSet.univ (hA n) (subset_univ _) hn

theorem cutoff_norm_limit_le_alphaTheta_univ
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0)) {c : ℝ}
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 c)) :
    c ≤ alphaTheta T univ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto hconv
  filter_upwards [eventually_cutOperatorNorm_lt_alphaTheta_univ_add T A hA hmass hε] with n hn
  apply le_trans (((lpCutL (A n) (hA n)).comp T).le_opNorm (f n))
  apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (hf n))
  simpa only [cutOperatorNorm_eq _ _ (hA n)] using hn.le

theorem extremal_cutoff_input_norm_tendsto_one
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (f : ℕ → LOne 𝕜 μ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n))
    (hmass : Tendsto (fun n => ν (A n)) atTop (𝓝 0))
    (hc : 0 < alphaTheta T univ)
    (hconv : Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
      (𝓝 (alphaTheta T univ))) : Tendsto (fun n => ‖f n‖) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall fun n => ha0.trans_le (norm_nonneg _)
    have ha0 : 0 ≤ a := le_of_not_gt ha0
    let c := alphaTheta T univ
    let ε := (1 - a) * c / 2
    have hε : 0 < ε := div_pos (mul_pos (sub_pos.mpr ha) hc) (by norm_num)
    have hprod : (c + ε) * a < c := by
      dsimp [ε]
      have hpos : 0 < (1 - a) * c := mul_pos (sub_pos.mpr ha) hc
      have hsq : 0 ≤ (1 - a) ^ 2 * c := mul_nonneg (sq_nonneg _) hc.le
      nlinarith
    filter_upwards [eventually_cutOperatorNorm_lt_alphaTheta_univ_add T A hA hmass hε,
      hconv.eventually (lt_mem_nhds hprod)] with n hop hq
    by_contra hn
    have hn : ‖f n‖ ≤ a := le_of_not_gt hn
    have hh := ((lpCutL (A n) (hA n)).comp T).le_opNorm (f n)
    have hb : ‖lpCut (A n) (hA n) (T (f n))‖ ≤ (c + ε) * a := by
      apply le_trans hh
      apply mul_le_mul _ hn (norm_nonneg _) (by dsimp [c]; linarith)
      simpa only [cutOperatorNorm_eq _ _ (hA n)] using hop.le
    exact (not_lt_of_ge hb) hq
  · intro b hb
    exact Eventually.of_forall fun n => (hf n).trans_lt hb

end PEMS
