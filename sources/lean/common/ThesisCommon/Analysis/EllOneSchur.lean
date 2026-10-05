import ThesisCommon.Analysis.EllOneSchurTest
import ThesisCommon.Analysis.SequenceCoordinates

/-! Schur's theorem for real ell-one on an arbitrary index set. Weak nullity
is tested against every genuine continuous linear functional. -/
noncomputable section
open scoped Topology
open Filter
namespace ThesisCommon
variable {I : Type*}

/-- In real ell-one, weak convergence of sequences to zero implies norm
convergence to zero. The index set need not be countable. -/
theorem ellOne_schur (u : ℕ → lp (fun _ : I => ℝ) 1)
    (hu : ∀ φ : lp (fun _ : I => ℝ) 1 →L[ℝ] ℝ,
      Tendsto (fun n => φ (u n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  suffices h : ∀ᶠ n in atTop, ‖u n‖ < ε by
    simpa only [dist_zero_right] using eventually_atTop.mp h
  by_contra h
  have hfreq : ∃ᶠ n in atTop, ε ≤ ‖u n‖ := by
    simpa only [not_lt] using (Filter.not_eventually.mp h)
  obtain ⟨s, hs, hsbound⟩ := extraction_of_frequently_atTop hfreq
  have hcoord (i : I) : Tendsto (fun n => u (s n) i) atTop (𝓝 0) :=
    (hu (lpCoordinate 1 i)).comp hs.tendsto_atTop
  obtain ⟨r, hr, φ, hφ⟩ := ellOne_subsequence_norm_test (fun n => u (s n)) hcoord
    (show 0 < ε / 4 by linarith)
  have ht : Tendsto (fun n => φ (u (s (r n)))) atTop (𝓝 0) :=
    ((hu φ).comp hs.tendsto_atTop).comp hr.tendsto_atTop
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  have hb := hsbound (r n)
  have hp := hφ n
  linarith

/-- The Schur property is invariant under Banach-space isomorphism. -/
theorem schur_of_equiv_ellOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (u : ℕ → E)
    (hu : ∀ φ : E →L[ℝ] ℝ, Tendsto (fun n => φ (u n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have ht := ellOne_schur (fun n => d (u n))
    (fun φ => hu (φ.comp d.toContinuousLinearMap))
  have h := (d.symm.continuous.tendsto 0).comp ht
  simpa only [Function.comp_def, d.symm_apply_apply, map_zero] using h

end ThesisCommon
