import ThesisCommon.Analysis.MilutinFiniteCover
import Mathlib.Topology.MetricSpace.Bounded

/-! Finite compact covers of arbitrarily small diameter, with duplicated labels.
These are the covering pieces in Ditor's construction of a Cantor inverse limit.
Duplicating labels ensures that each point has at least two labelled lifts. -/

noncomputable section
open Set Metric
namespace ThesisCommon
variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]

theorem milutin_small_compact_cover (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (s : Fin n → Set K),
      2 ≤ n ∧
      (∀ i, IsCompact (s i) ∧ (s i).Nonempty ∧ Metric.diam (s i) < ε) ∧
      (∀ x : K, ∃ i, x ∈ interior (s i)) ∧
      (∀ x : K, ∃ i j, i ≠ j ∧ x ∈ s i ∧ x ∈ s j) := by
  classical
  obtain ⟨t, _, htfin, ht⟩ := finite_cover_balls_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set K)) (show 0 < ε / 4 by positivity)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty K›
    obtain ⟨a, ha, _⟩ : ∃ a ∈ t, x ∈ Metric.ball a (ε / 4) := by
      simpa only [mem_iUnion, exists_prop] using ht (mem_univ x)
    exact ⟨a, ha⟩
  letI : Fintype t := htfin.fintype
  letI : Nonempty t := htne.to_subtype
  let e := Fintype.equivFin (t × Bool)
  let s : Fin (Fintype.card (t × Bool)) → Set K :=
    fun i => Metric.closedBall ((e.symm i).1 : K) (ε / 4)
  refine ⟨Fintype.card (t × Bool), s, ?_, ?_, ?_, ?_⟩
  · have hpos := Fintype.card_pos (α := t)
    simp only [Fintype.card_prod, Fintype.card_bool]
    omega
  · intro i
    refine ⟨isClosed_closedBall.isCompact, ?_, ?_⟩
    · exact ⟨((e.symm i).1 : K), Metric.mem_closedBall_self (by positivity)⟩
    · exact (Metric.diam_closedBall (show 0 ≤ ε / 4 by positivity)).trans_lt (by linarith)
  · intro x
    obtain ⟨a, ha, hxa⟩ : ∃ a ∈ t, x ∈ Metric.ball a (ε / 4) := by
      simpa only [mem_iUnion, exists_prop] using ht (mem_univ x)
    refine ⟨e (⟨a, ha⟩, true), ?_⟩
    simpa only [s, Equiv.symm_apply_apply] using Metric.ball_subset_interior_closedBall hxa
  · intro x
    obtain ⟨a, ha, hxa⟩ : ∃ a ∈ t, x ∈ Metric.ball a (ε / 4) := by
      simpa only [mem_iUnion, exists_prop] using ht (mem_univ x)
    refine ⟨e (⟨a, ha⟩, true), e (⟨a, ha⟩, false), ?_, ?_, ?_⟩
    · intro h
      have he := congrArg Prod.snd (e.injective h)
      cases he
    · simpa only [s, Equiv.symm_apply_apply] using Metric.ball_subset_closedBall hxa
    · simpa only [s, Equiv.symm_apply_apply] using Metric.ball_subset_closedBall hxa

end ThesisCommon
