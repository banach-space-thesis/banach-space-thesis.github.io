import ThesisCommon.Analysis.DyadicSubtreeFusion
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

/-! Summable branch variation on an actual selected dyadic subtree.
Every branch may start at an arbitrary node. The metric formulation applies
to both real and complex bounded scalar functions, with no sign assumption. -/
noncomputable section
open Filter Topology
namespace ThesisCommon

def dyadicBranchPath (b : ℕ → Bool) : ℕ → DyadicTreeNode
  | 0 => []
  | n + 1 => dyadicBranchPath b n ++ [b n]

@[simp] theorem dyadicBranchPath_length (b : ℕ → Bool) (n : ℕ) :
    (dyadicBranchPath b n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dyadicBranchPath, List.length_append, ih, List.length_singleton]

theorem dyadicBranchPath_prefix (b : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    (dyadicBranchPath b n).IsPrefix (dyadicBranchPath b m) := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m _ ih => exact ih.trans (List.prefix_append _ _)

theorem exists_dyadic_subtree_branch_limits {K : Type*} [MetricSpace K] [CompleteSpace K]
    (f : DyadicTreeNode → K) (hf : TotallyBounded (Set.range f))
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδsum : Summable δ) :
    ∃ e : DyadicSubtreeEmbedding, ∀ u : DyadicTreeNode, ∀ b : ℕ → Bool, ∃ L : K,
      Tendsto (fun n => f (e (u ++ dyadicBranchPath b n))) atTop (𝓝 L) ∧
      (∀ n, dist (f (e (u ++ dyadicBranchPath b n))) L ≤ δ (u.length + n)) ∧
      Summable (fun n => dist (f (e (u ++ dyadicBranchPath b n))) L) ∧
      (∑' n, dist (f (e (u ++ dyadicBranchPath b n))) L) ≤ ∑' n, δ n := by
  obtain ⟨e, he⟩ := exists_dyadic_subtree_descendant_oscillation f hf δ hδ
  refine ⟨e, ?_⟩
  intro u b
  let v (n : ℕ) := f (e (u ++ dyadicBranchPath b n))
  have htail : Summable (fun n => δ (u.length + n)) :=
    hδsum.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hdist (n m : ℕ) (hnm : n ≤ m) : dist (v n) (v m) ≤ δ (u.length + n) := by
    have h := he (u ++ dyadicBranchPath b n) (u ++ dyadicBranchPath b m)
      ((List.prefix_append_right_inj u).mpr (dyadicBranchPath_prefix b hnm))
    simpa only [List.length_append, dyadicBranchPath_length] using h.le
  have hc : CauchySeq v := cauchySeq_of_le_tendsto_0' _ hdist htail.tendsto_atTop_zero
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hlimit (n : ℕ) : dist (v n) L ≤ δ (u.length + n) :=
    le_of_tendsto (tendsto_const_nhds.dist hL)
      ((eventually_ge_atTop n).mono (fun m hm => hdist n m hm))
  have hsum : Summable (fun n => dist (v n) L) :=
    htail.of_nonneg_of_le (fun _ => dist_nonneg) hlimit
  refine ⟨L, hL, hlimit, hsum, ?_⟩
  calc
    _ ≤ ∑' n, δ (u.length + n) := Summable.tsum_le_tsum hlimit hsum htail
    _ ≤ ∑' n, δ n := Summable.tsum_le_tsum_of_inj (fun n => u.length + n)
      (fun _ _ h => Nat.add_left_cancel h) (fun n _ => (hδ n).le)
      (fun _ => le_rfl) htail hδsum

theorem exists_dyadic_subtree_branch_variation {K : Type*} [MetricSpace K] [CompleteSpace K]
    (f : DyadicTreeNode → K) (hf : TotallyBounded (Set.range f))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : DyadicSubtreeEmbedding, ∀ u : DyadicTreeNode, ∀ b : ℕ → Bool, ∃ L : K,
      Tendsto (fun n => f (e (u ++ dyadicBranchPath b n))) atTop (𝓝 L) ∧
      Summable (fun n => dist (f (e (u ++ dyadicBranchPath b n))) L) ∧
      (∑' n, dist (f (e (u ++ dyadicBranchPath b n))) L) < ε := by
  let δ (n : ℕ) : ℝ := (ε / 4) * (1 / 2 : ℝ) ^ n
  have hδ (n) : 0 < δ n := by dsimp [δ]; positivity
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hδsum : Summable δ := hg.mul_left _
  have hsum : (∑' n, δ n) = ε / 2 := by
    rw [show δ = (fun n => (ε / 4) * (1 / 2 : ℝ) ^ n) from rfl, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
    ring
  obtain ⟨e, he⟩ := exists_dyadic_subtree_branch_limits f hf δ hδ hδsum
  refine ⟨e, ?_⟩
  intro u b
  obtain ⟨L, hL, _, hsumL, hbound⟩ := he u b
  refine ⟨L, hL, hsumL, ?_⟩
  rw [hsum] at hbound
  linarith

theorem exists_dyadic_scalar_subtree_branch_variation {𝕜 : Type*} [RCLike 𝕜]
    (f : DyadicTreeNode → 𝕜) (M : ℝ) (hf : ∀ t, ‖f t‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : DyadicSubtreeEmbedding, ∀ u : DyadicTreeNode, ∀ b : ℕ → Bool, ∃ L : 𝕜,
      Tendsto (fun n => f (e (u ++ dyadicBranchPath b n))) atTop (𝓝 L) ∧
      Summable (fun n => ‖f (e (u ++ dyadicBranchPath b n)) - L‖) ∧
      (∑' n, ‖f (e (u ++ dyadicBranchPath b n)) - L‖) < ε := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have htotal : TotallyBounded (Set.range f) :=
    (isCompact_closedBall (0 : 𝕜) M).totallyBounded.subset (by
      rintro _ ⟨t, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hf t)
  simpa only [dist_eq_norm] using exists_dyadic_subtree_branch_variation f htotal hε

end ThesisCommon
