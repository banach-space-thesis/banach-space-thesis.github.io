import ThesisCommon.Analysis.JamesSequenceSpace
import Mathlib.Topology.MetricSpace.Cauchy

/-! Completeness in the James variation norm. Contractivity into c₀ gives a
null-sequence limit. Continuity of each finite-path map preserves uniform
path bounds, and the Cauchy estimates then give convergence in James norm.
-/
noncomputable section
open Filter Topology
namespace ThesisCommon.JamesSequenceSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent}

/-- Lower semicontinuity of James norm under convergence in the c₀ norm. -/
theorem norm_le_of_cZero_limit (u : ℕ → JamesSequenceSpace 𝕜 p)
    (x : JamesSequenceSpace 𝕜 p)
    (hx : Tendsto (fun k => (u k).val) atTop (𝓝 x.val))
    {C : ℝ} (hC : ∀ᶠ k in atTop, ‖u k‖ ≤ C) : ‖x‖ ≤ C := by
  apply norm_le
  intro s
  apply le_of_tendsto (((jamesPathMap 𝕜 p s).continuous.tendsto x.val).comp hx).norm
  filter_upwards [hC] with k hk
  exact (path_norm_le (u k) s).trans hk

instance instCompleteSpace : CompleteSpace (JamesSequenceSpace 𝕜 p) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc : CauchySeq (fun k => (u k).val) :=
    (toCZero (𝕜 := 𝕜) (p := p)).uniformContinuous.comp_cauchySeq hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu 1 zero_lt_one
  have hbounded (k : ℕ) (hk : N ≤ k) : ‖u k‖ ≤ 1 + ‖u N‖ := by
    calc
      ‖u k‖ = ‖(u k - u N) + u N‖ := by rw [sub_add_cancel]
      _ ≤ ‖u k - u N‖ + ‖u N‖ := norm_add_le _ _
      _ ≤ 1 + ‖u N‖ := add_le_add
        (show ‖u k - u N‖ ≤ 1 from
          le_of_lt (by simpa only [dist_eq_norm] using hN k hk N le_rfl)) le_rfl
  have hy_mem : HasBoundedJamesVariation 𝕜 p y := by
    refine ⟨1 + ‖u N‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    apply le_of_tendsto (((jamesPathMap 𝕜 p s).continuous.tendsto y).comp hy).norm
    filter_upwards [eventually_ge_atTop N] with k hk
    exact (path_norm_le (u k) s).trans (hbounded k hk)
  let x : JamesSequenceSpace 𝕜 p := ⟨y, hy_mem⟩
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨M, ?_⟩
  intro k hk
  rw [dist_eq_norm]
  have hbound : ‖u k - x‖ ≤ ε / 2 := by
    apply norm_le_of_cZero_limit (fun j => u k - u j) (u k - x)
    · exact tendsto_const_nhds.sub hy
    · filter_upwards [eventually_ge_atTop M] with j hj
      exact (show ‖u k - u j‖ < ε / 2 from by
        simpa only [dist_eq_norm] using hM k hk j hj).le
  exact hbound.trans_lt (half_lt_self hε)

end ThesisCommon.JamesSequenceSpace
