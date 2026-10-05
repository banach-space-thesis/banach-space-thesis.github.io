import ThesisCommon.Analysis.JamesShrinkingWitnesses

/-! The actual coordinate basis of James space is shrinking for 1 < p < ∞.
Every continuous scalar functional is the norm limit of its finite
coordinate expansions; consequently the bidual is determined by the
values on coordinate functionals. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_functional_late_small (hpl : 1 < p.val.toReal)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : JamesSequenceSpace 𝕜 p, (∀ n ≤ N, x n = 0) →
      ‖φ x‖ ≤ ε * ‖x‖ := by
  by_contra h
  push_neg at h
  exact james_no_disjoint_functional_witnesses p hp hpl φ hε zero_le_one
    (james_finite_disjoint_witnesses p hp φ hε h)

include hp in
set_option maxHeartbeats 800000 in
theorem james_functional_initial_tendsto (hpl : 1 < p.val.toReal)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) :
    Tendsto (fun N => φ.comp (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N))
      atTop (𝓝 φ) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := james_functional_late_small p hp hpl φ
    (show 0 < ε / 4 by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have heq : φ - φ.comp (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) n) =
      φ.comp (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) n) := by
    ext x
    simp [JamesSequenceSpace.tail]
  rw [dist_eq_norm, norm_sub_rev, heq]
  have hbound : ‖φ.comp (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) n)‖ ≤ ε / 2 := by
    refine (φ.comp (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) n)).opNorm_le_bound
      (by positivity) ?_
    intro x
    have hz : ∀ k ≤ N, (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) n x) k = 0 := by
      intro k hk
      simp [JamesSequenceSpace.tail_apply, hk.trans hn]
    have htail := (JamesSequenceSpace.tail (𝕜 := 𝕜) (p := p) n).le_of_opNorm_le
      (JamesSequenceSpace.norm_tail_le (𝕜 := 𝕜) (p := p) n) x
    apply (hN _ hz).trans
    calc
      _ ≤ (ε / 4) * (2 * ‖x‖) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  exact hbound.trans_lt (half_lt_self hε)

theorem james_functional_initial_eq_sum
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) (N : ℕ) :
    φ.comp (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N) =
      ∑ n ∈ Finset.range (N + 1),
        φ (jamesUnit p hp n) • JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n := by
  ext x
  change φ (JamesSequenceSpace.initial (𝕜 := 𝕜) (p := p) N x) = _
  rw [← james_finite_units_eq_initial p hp N x]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n _
  change x n * φ (jamesUnit p hp n) = φ (jamesUnit p hp n) * x n
  exact mul_comm _ _

theorem james_dual_finite_coordinates_tendsto (hpl : 1 < p.val.toReal)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      φ (jamesUnit p hp n) • JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)
      atTop (𝓝 φ) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [← james_functional_initial_eq_sum p hp] using
    james_functional_initial_tendsto p hp hpl φ

include hp in
theorem james_bidual_ext_coordinates (hpl : 1 < p.val.toReal)
    {ξ ζ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜}
    (h : ∀ n, ξ (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n) =
      ζ (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)) : ξ = ζ := by
  apply ContinuousLinearMap.ext
  intro φ
  have ht := james_dual_finite_coordinates_tendsto p hp hpl φ
  have hξ := (ξ.continuous.tendsto φ).comp ht
  have hζ := (ζ.continuous.tendsto φ).comp ht
  have heq : (fun N => ξ (∑ n ∈ Finset.range N,
      φ (jamesUnit p hp n) • JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)) =
      (fun N => ζ (∑ n ∈ Finset.range N,
      φ (jamesUnit p hp n) • JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) n)) := by
    funext N
    simp only [map_sum, map_smul, h]
  simp only [Function.comp_def] at hξ hζ
  rw [heq] at hξ
  exact tendsto_nhds_unique hξ hζ

end ThesisCommon
