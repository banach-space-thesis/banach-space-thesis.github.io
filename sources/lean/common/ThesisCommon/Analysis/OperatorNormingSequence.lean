import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Order.IsLUB

/-! Countable norm witnesses for a genuine bounded real linear operator. -/
noncomputable section
open Set Filter Topology Metric
namespace ThesisCommon
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_operator_norming_sequence (T : E →L[ℝ] F) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ ≤ 1) ∧
      Tendsto (fun n => ‖T (f n)‖) atTop (𝓝 ‖T‖) := by
  have hb : BddAbove ((fun x => ‖T x‖) '' closedBall (0 : E) 1) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact T.unit_le_opNorm x (mem_closedBall_zero_iff.mp hx)
  obtain ⟨r, _, ht, hr⟩ := exists_seq_tendsto_sSup
    ((nonempty_closedBall.mpr zero_le_one).image (fun x => ‖T x‖)) hb
  choose f hf heq using hr
  refine ⟨f, fun n => mem_closedBall_zero_iff.mp (hf n), ?_⟩
  simpa only [heq, T.sSup_unitClosedBall_eq_norm] using ht

theorem norm_comp_isometry_eq_of_norming_sequence
    (T : E →L[ℝ] F) (e : G →ₗᵢ[ℝ] E) (f : ℕ → E)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (ht : Tendsto (fun n => ‖T (f n)‖) atTop (𝓝 ‖T‖))
    (hmem : ∀ n, f n ∈ Set.range e) :
    ‖T.comp e.toContinuousLinearMap‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      e.norm_map] using T.le_opNorm (e x)
  · apply le_of_tendsto' ht
    intro n
    obtain ⟨g, hg⟩ := hmem n
    have hgnorm : ‖g‖ ≤ 1 := by rw [← e.norm_map, hg]; exact hf n
    rw [← hg]
    exact (T.comp e.toContinuousLinearMap).unit_le_opNorm g hgnorm

end ThesisCommon
