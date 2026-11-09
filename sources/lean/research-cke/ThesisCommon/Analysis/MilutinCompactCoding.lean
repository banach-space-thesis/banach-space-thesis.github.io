import ThesisCommon.Analysis.MilutinCompactSystem
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Finite component labels separate points of Ditor's actual inverse limit.
The geometric mesh forces equal label codes to represent equal points. -/

noncomputable section
open Filter Set Topology
namespace ThesisCommon

theorem milutinCoverStep_dist_eq {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
    {ε : ℝ} (S : MilutinCoverStep K ε) (x y : S.Space) (h : x.1 = y.1) :
    dist x y = dist (S.projection x) (S.projection y) := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  cases h
  exact S.dist_same_piece i x y

theorem milutinCoverStep_projection_dist_lt {K : Type*} [MetricSpace K]
    [CompactSpace K] [Nonempty K] {ε : ℝ} (S : MilutinCoverStep K ε)
    (x y : S.Space) (h : x.1 = y.1) :
    dist (S.projection x) (S.projection y) < ε := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  cases h
  exact (Metric.dist_le_diam_of_mem (S.compact i).isBounded x.property y.property).trans_lt (S.small i)

theorem milutinMesh_tendsto : Tendsto milutinMesh atTop (𝓝 0) := by
  simpa only [milutinMesh, pow_succ, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)

theorem milutinCompactCode_injective (B : MilutinCompactMetric) :
    Function.Injective (milutinCompactCode B) := by
  intro x y hxy
  have hlab (n : ℕ) : (x.val (n + 1)).1 = (y.val (n + 1)).1 := congrFun hxy n
  have hstep (n : ℕ) : dist (x.val (n + 1)) (y.val (n + 1)) = dist (x.val n) (y.val n) := by
    have h := milutinCoverStep_dist_eq (milutinCompactCover B n)
      (x.val (n + 1)) (y.val (n + 1)) (hlab n)
    change dist (x.val (n + 1)) (y.val (n + 1)) =
      dist (milutinCompactBonding B n (x.val (n + 1)))
        (milutinCompactBonding B n (y.val (n + 1))) at h
    rw [x.property n, y.property n] at h
    exact h
  have hconstant (n : ℕ) : dist (x.val n) (y.val n) = dist (x.val 0) (y.val 0) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hstep n).trans ih
  have hsmall (n : ℕ) : dist (x.val 0) (y.val 0) ≤ milutinMesh n := by
    have h := milutinCoverStep_projection_dist_lt (milutinCompactCover B n)
      (x.val (n + 1)) (y.val (n + 1)) (hlab n)
    change dist (milutinCompactBonding B n (x.val (n + 1)))
      (milutinCompactBonding B n (y.val (n + 1))) < milutinMesh n at h
    rw [x.property n, y.property n, hconstant n] at h
    exact h.le
  have hz : dist (x.val 0) (y.val 0) = 0 := le_antisymm
    (ge_of_tendsto milutinMesh_tendsto
      (show ∀ᶠ n in atTop, dist (x.val 0) (y.val 0) ≤ milutinMesh n from
        Eventually.of_forall hsmall)) dist_nonneg
  apply Subtype.ext
  funext n
  apply dist_eq_zero.mp
  exact (hconstant n).trans hz

theorem milutinCompactCode_isClosedEmbedding (B : MilutinCompactMetric) :
    IsClosedEmbedding (milutinCompactCode B) :=
  (milutinCompactCode B).continuous.isClosedEmbedding (milutinCompactCode_injective B)

instance milutinCompactLimitTotallyDisconnected (B : MilutinCompactMetric) :
    TotallyDisconnectedSpace (MilutinCompactLimit B) := by
  apply (milutinCompactCode_isClosedEmbedding B).isEmbedding.isTotallyDisconnected_range.mp
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

end ThesisCommon
