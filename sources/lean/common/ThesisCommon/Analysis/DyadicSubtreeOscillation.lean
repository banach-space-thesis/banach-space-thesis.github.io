import ThesisCommon.Analysis.DyadicSubtreeSelection
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Finite-cover selection produces an actual subtree on which a scalar
or metric-valued function has uniformly small oscillation. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [PseudoMetricSpace K]

theorem exists_dyadic_subtree_small_oscillation (f : DyadicTreeNode → K)
    (hf : TotallyBounded (Set.range f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : DyadicSubtreeEmbedding, ∀ s t, dist (f (e s)) (f (e t)) < ε := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp hf (ε / 2) (by positivity)
  have hc : ∀ t, ∃ c ∈ hC.toFinset, dist (f t) c < ε / 2 := by
    intro t
    obtain ⟨c, hc, ht⟩ := Set.mem_iUnion₂.mp (hcover ⟨t, rfl⟩)
    exact ⟨c, hC.mem_toFinset.mpr hc, ht⟩
  obtain ⟨c, _, e, he⟩ := exists_dyadic_subtree_in_finite_cover hC.toFinset
    (fun c t => dist (f t) c < ε / 2) hc
  refine ⟨e, fun s t => ?_⟩
  have hs := he s
  have ht := he t
  have htri := dist_triangle (f (e s)) c (f (e t))
  rw [dist_comm c] at htri
  linarith

def dyadicOscillationSubtree (f : DyadicTreeNode → K)
    (hf : TotallyBounded (Set.range f)) (ε : ℝ) (hε : 0 < ε) : DyadicSubtreeEmbedding :=
  Classical.choose (exists_dyadic_subtree_small_oscillation f hf hε)

theorem dyadicOscillationSubtree_bound (f : DyadicTreeNode → K)
    (hf : TotallyBounded (Set.range f)) (ε : ℝ) (hε : 0 < ε) (s t : DyadicTreeNode) :
    dist (f (dyadicOscillationSubtree f hf ε hε s))
      (f (dyadicOscillationSubtree f hf ε hε t)) < ε :=
  Classical.choose_spec (exists_dyadic_subtree_small_oscillation f hf hε) s t

end ThesisCommon
