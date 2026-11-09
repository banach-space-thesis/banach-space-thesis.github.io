import SurveyStatements.P1RamseyFusion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Compactness of bounded complex scalar sequences supplies two actual
cluster values from persistent tail oscillation. -/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace SurveyStatements.P1

theorem bounded_complex_tail_oscillation_cluster_pair (u : ℕ → ℂ) {M δ : ℝ}
    (hM : ∀ n, ‖u n‖ ≤ M)
    (hosc : ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, δ ≤ ‖u m - u n‖) :
    ∃ z w : ℂ, ‖z‖ ≤ M ∧ ‖w‖ ≤ M ∧ δ ≤ ‖z - w‖ ∧
      ∃ p q : ℕ → ℕ, Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
        Tendsto (u ∘ p) atTop (𝓝 z) ∧ Tendsto (u ∘ q) atTop (𝓝 w) := by
  classical
  choose m hm n hn hdist using hosc
  have hin (k : ℕ) : (u (m k), u (n k)) ∈
      Metric.closedBall (0 : ℂ) M ×ˢ Metric.closedBall (0 : ℂ) M := by
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hM (m k),
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hM (n k)⟩
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    ((isCompact_closedBall (0 : ℂ) M).prod (isCompact_closedBall (0 : ℂ) M)).tendsto_subseq hin
  have hp : Tendsto (m ∘ φ) atTop atTop :=
    tendsto_atTop_mono (fun k => hm (φ k)) hφ.tendsto_atTop
  have hq : Tendsto (n ∘ φ) atTop atTop :=
    tendsto_atTop_mono (fun k => hn (φ k)) hφ.tendsto_atTop
  have hz : Tendsto (u ∘ (m ∘ φ)) atTop (𝓝 v.1) := (continuous_fst.tendsto v).comp hlim
  have hw : Tendsto (u ∘ (n ∘ φ)) atTop (𝓝 v.2) := (continuous_snd.tendsto v).comp hlim
  have hδ : δ ≤ ‖v.1 - v.2‖ := by
    apply ge_of_tendsto (hz.sub hw).norm
    exact Eventually.of_forall (fun k => hdist (φ k))
  refine ⟨v.1, v.2, ?_, ?_, hδ, m ∘ φ, n ∘ φ, hp, hq, hz, hw⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hv.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hv.2

theorem bounded_complex_not_cauchy_cluster_pair (u : ℕ → ℂ) {M : ℝ}
    (hM : ∀ n, ‖u n‖ ≤ M) (hnot : ¬ CauchySeq u) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ z w : ℂ, ‖z‖ ≤ M ∧ ‖w‖ ≤ M ∧ δ ≤ ‖z - w‖ ∧
      ∃ p q : ℕ → ℕ, Tendsto p atTop atTop ∧ Tendsto q atTop atTop ∧
        Tendsto (u ∘ p) atTop (𝓝 z) ∧ Tendsto (u ∘ q) atTop (𝓝 w) := by
  rw [Metric.cauchySeq_iff] at hnot
  push_neg at hnot
  obtain ⟨δ, hδ, hosc⟩ := hnot
  refine ⟨δ, hδ, bounded_complex_tail_oscillation_cluster_pair u hM ?_⟩
  intro N
  obtain ⟨m, hm, n, hn, hdist⟩ := hosc N
  exact ⟨m, hm, n, hn, by simpa only [dist_eq_norm] using hdist⟩

end SurveyStatements.P1
