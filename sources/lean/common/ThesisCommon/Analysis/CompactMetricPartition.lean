import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! A finite positive continuous partition on a compact metric space,
subordinate to balls of half the prescribed diameter. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {K : Type*} [MetricSpace K] [CompactSpace K]

theorem exists_finite_metric_partition {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset K, ∃ p : s → C(K, ℝ),
      (∀ i x, 0 ≤ p i x) ∧ (∀ x, ∑ i, p i x = 1) ∧
      (∀ i x, p i x ≠ 0 → dist x i.val < ε / 2) := by
  classical
  let U : K → Set K := fun x => Metric.ball x (ε/2)
  have hcover : (Set.univ : Set K) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,by simpa [U] using (half_pos hε)⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (Set.univ : Set K) ⊆ ⋃ i : s, U i.val := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨p,hp⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : s => U i.val) (fun _ => Metric.isOpen_ball) hcover'
  refine ⟨s,p,fun i x => p.nonneg i x,?_,?_⟩
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one (Set.mem_univ x)
  · intro i x hx
    exact hp i (subset_closure hx)

end ThesisCommon
