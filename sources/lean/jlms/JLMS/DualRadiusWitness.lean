import JLMS.DualRadiusScaling
import JLMS.PhaseFunctions
import Mathlib.Topology.Sequences

/-!
# Unit vectors witnessing a positive asymptotic radius

Failure of a smaller eventual bound gives a fixed unit vector with large
values along a subsequence. Compactness of the scalar ball then permits a
single rotation of this vector, giving large positive real parts on a
further subsequence over either scalar field.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_unit_frequently_norm_gt (f : ℕ → (X →L[𝕜] 𝕜)) {r : ℝ}
    (hr : 0 ≤ r) (hlt : r < dualAsymptoticRadius f) :
    ∃ x : X, ‖x‖ = 1 ∧ ∃ᶠ n in atTop, r < ‖f n x‖ := by
  classical
  have hnot : ¬ DualEventualBound f r := fun h =>
    (not_le_of_gt hlt) (dualAsymptoticRadius_le f hr h)
  simp only [DualEventualBound, not_forall] at hnot
  obtain ⟨x, ε, hε, hbad⟩ := hnot
  have hfreq : ∃ᶠ n in atTop, (r + ε) * ‖x‖ < ‖f n x‖ := by
    simpa only [Filter.Frequently, not_lt] using hbad
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simpa using hfreq
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y := (‖x‖⁻¹ : 𝕜) • x
  have hy : ‖y‖ = 1 := by
    simp only [y, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hnx.ne']
  refine ⟨y, hy, hfreq.mono (fun n hn => ?_)⟩
  have hn' : r * ‖x‖ < ‖f n x‖ := by nlinarith
  simp only [y, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x)]
  exact (lt_inv_mul_iff₀ hnx).mpr (by simpa only [mul_comm] using hn')

theorem exists_unit_real_subsequence_gt (f : ℕ → (X →L[𝕜] 𝕜)) {C r : ℝ}
    (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (hr : 0 ≤ r) (hlt : r < dualAsymptoticRadius f) :
    ∃ x : X, ‖x‖ = 1 ∧ ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ n, r < RCLike.re (f (s n) x) := by
  let q := (r + dualAsymptoticRadius f) / 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hqδ : q < dualAsymptoticRadius f := by dsimp [q]; linarith
  obtain ⟨x, hx, hfreq⟩ := exists_unit_frequently_norm_gt f hq hqδ
  obtain ⟨s, hs, hlarge⟩ := Filter.extraction_of_frequently_atTop hfreq
  let B := ↥(Metric.closedBall (0 : 𝕜) C)
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hball (n : ℕ) : f (s n) x ∈ Metric.closedBall (0 : 𝕜) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa only [hx, mul_one] using ((f (s n)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hf _) (norm_nonneg x))
  let u (n : ℕ) : B := ⟨f (s n) x, hball n⟩
  obtain ⟨z, t, ht, hlim⟩ := SeqCompactSpace.tendsto_subseq u
  have hzlim : Tendsto (fun n => f (s (t n)) x) atTop (𝓝 z.val) :=
    continuous_subtype_val.tendsto z |>.comp hlim
  have hzlarge : q ≤ ‖z.val‖ :=
    ge_of_tendsto hzlim.norm (Eventually.of_forall (fun n => (hlarge (t n)).le))
  let y := scalarPhase z.val • x
  have hy : ‖y‖ = 1 := by rw [norm_smul, norm_scalarPhase, hx, one_mul]
  have hreal : Tendsto (fun n => RCLike.re (f (s (t n)) y)) atTop (𝓝 ‖z.val‖) := by
    have hh := RCLike.continuous_re.tendsto (scalarPhase z.val * z.val) |>.comp
      ((tendsto_const_nhds (x := scalarPhase z.val)).mul hzlim)
    simpa only [y, map_smul, smul_eq_mul, scalarPhase_mul, RCLike.ofReal_re] using hh
  have hev : ∀ᶠ n in atTop, r < RCLike.re (f (s (t n)) y) :=
    (tendsto_order.mp hreal).1 r (by dsimp [q] at hzlarge; linarith)
  obtain ⟨v, hv, hgood⟩ := Filter.extraction_of_eventually_atTop hev
  exact ⟨y, hy, fun n => s (t (v n)), hs.comp (ht.comp hv), hgood⟩

end JLMS
