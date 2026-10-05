import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Clopen neighborhoods in countable metric spaces. Choosing a radius
outside the countable set of distances makes an open ball also closed.
This supplies the local decompositions needed by transfinite classification
of countable compact metric spaces. -/

noncomputable section
open Set Metric
namespace ThesisCommon
variable {K : Type*} [MetricSpace K] [Countable K]

theorem countableMetric_exists_clopen_ball (x : K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ IsClopen (Metric.ball x r) := by
  have hd := (Set.countable_range (fun y : K => dist y x)).dense_compl ℝ
  obtain ⟨r, hdist, hr⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hε)
  have hballs : Metric.closedBall x r = Metric.ball x r := by
    ext y
    simp only [Metric.mem_closedBall, Metric.mem_ball]
    constructor
    · intro hy
      apply lt_of_le_of_ne hy
      intro h
      exact hdist ⟨y, h⟩
    · exact fun hy => le_of_lt hy
  exact ⟨r, hr.1, hr.2, ⟨hballs ▸ isClosed_closedBall, isOpen_ball⟩⟩

theorem countableMetric_exists_clopen_nhds (x : K) {U : Set K} (hU : U ∈ nhds x) :
    ∃ V : Set K, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrε, hrclopen⟩ := countableMetric_exists_clopen_ball x hε
  exact ⟨Metric.ball x r, hrclopen, Metric.mem_ball_self hr,
    (Metric.ball_subset_ball hrε.le).trans hball⟩

theorem countableMetric_totallySeparatedSpace : TotallySeparatedSpace K := by
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨r, hr, hrd, hc⟩ := countableMetric_exists_clopen_ball x hd
  refine ⟨Metric.ball x r, hc, Metric.mem_ball_self hr, ?_⟩
  change ¬ dist y x < r
  rw [dist_comm]
  exact (le_of_lt hrd).not_gt

end ThesisCommon
