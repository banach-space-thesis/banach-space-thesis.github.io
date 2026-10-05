import ThesisCommon.Analysis.EllOneSchurFunctional
import ThesisCommon.Analysis.FiniteHistory
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The disjoint finite blocks in the arbitrary-index ell-one Schur argument. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ThesisCommon
variable {I : Type*}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem ellOne_norm_tail (x : lp (fun _ : I => ℝ) 1) (F : Finset I) :
    ‖x - ∑ i ∈ F, lp.single 1 i (x i)‖ = ‖x‖ - ∑ i ∈ F, ‖x i‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp.norm_compl_sum_single (by norm_num : 0 < (1 : ENNReal).toReal) x F

theorem ellOne_norm_tail_sdiff_le (x : lp (fun _ : I => ℝ) 1) (F G : Finset I) :
    ‖x - ∑ i ∈ F \ G, lp.single 1 i (x i)‖ ≤
      ‖x - ∑ i ∈ F, lp.single 1 i (x i)‖ + ∑ i ∈ G, ‖x i‖ := by
  rw [ellOne_norm_tail, ellOne_norm_tail]
  have hp := F.sum_inter_add_sum_diff G (fun i => ‖x i‖)
  have hle : ∑ i ∈ F ∩ G, ‖x i‖ ≤ ∑ i ∈ G, ‖x i‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => norm_nonneg _)
  linarith

/-- A coordinatewise null sequence admits a subsequence uniformly approximated
by pairwise disjoint finite coordinate blocks, to any prescribed precision. -/
theorem ellOne_disjoint_finite_blocks (u : ℕ → lp (fun _ : I => ℝ) 1)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ B : ℕ → Finset I,
      Pairwise (fun m n => Disjoint (B m) (B n)) ∧
      ∀ n, ‖u (r n) - ∑ i ∈ B n, lp.single 1 i (u (r n) i)‖ < ε := by
  choose F hF using fun n => ellOne_exists_finite_approx (u n) (half_pos hε)
  have hsmall (G : Finset I) : ∀ᶠ n in atTop, ∑ i ∈ G, ‖u n i‖ < ε / 2 := by
    have ht : Tendsto (fun n => ∑ i ∈ G, ‖u n i‖) atTop (𝓝 0) := by
      simpa only [norm_zero, Finset.sum_const_zero] using
        tendsto_finset_sum G (fun i _ => (hu i).norm)
    exact ht.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨r, hr, _, hpast⟩ := increasing_finite_history Set.univ
    (fun n H => ∑ i ∈ H.biUnion F, ‖u n i‖ < ε / 2) (by
      intro H _
      obtain ⟨n, hn, hmass⟩ := ((eventually_gt_atTop (H.sup id)).and (hsmall (H.biUnion F))).exists
      exact ⟨n, Set.mem_univ _, fun m hm => (Finset.le_sup (f := id) hm).trans_lt hn, hmass⟩)
  let G (n : ℕ) := ((Finset.range n).image r).biUnion F
  let B (n : ℕ) := F (r n) \ G n
  have hbefore {m n : ℕ} (hmn : m < n) : Disjoint (B m) (B n) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have him := (Finset.mem_sdiff.mp hi).1
    have hin := (Finset.mem_sdiff.mp hj).2
    apply hin
    exact Finset.mem_biUnion.mpr ⟨r m,
      Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmn, rfl⟩, him⟩
  refine ⟨r, hr, B, fun m n hmn => ?_, fun n => ?_⟩
  · rcases lt_or_gt_of_ne hmn with h | h
    · exact hbefore h
    · exact (hbefore h).symm
  · exact (ellOne_norm_tail_sdiff_le (u (r n)) (F (r n)) (G n)).trans_lt
      (by have := hpast n; have := hF (r n); dsimp [G] at *; linarith)

end ThesisCommon
