import ThesisCommon.Analysis.EllOneSchur
import ThesisCommon.WeakCompact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Separation.Hausdorff
import ThesisCommon.Analysis.LpOneRestriction

/-! Weakly compact subsets of countable real ell-one are norm compact.
Coordinate evaluation embeds each compact weak subspace into the countable
product of real lines. That subspace is therefore first countable, so the
proved Schur theorem yields continuity of the map back to the norm topology.
No sequential weak-compactness theorem is assumed. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
abbrev CountableEllOne := lp (fun _ : ℕ => ℝ) 1

theorem weakEllOne_compact_firstCountable
    {K : Set (WeakSpace ℝ CountableEllOne)} (hK : IsCompact K) : FirstCountableTopology K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let c : K → (ℕ → ℝ) := fun x n => (toWeakSpace ℝ CountableEllOne).symm x.val n
  have hc : Continuous c := by
    apply continuous_pi
    intro n
    exact (WeakBilin.eval_continuous (topDualPairing ℝ CountableEllOne).flip
      (lpCoordinate 1 n)).comp continuous_subtype_val
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    apply (toWeakSpace ℝ CountableEllOne).symm.injective
    apply lp.ext
    exact hxy
  exact (hc.isClosedEmbedding hinj).isEmbedding.firstCountableTopology

theorem weakEllOne_compact_norm_continuous
    {K : Set (WeakSpace ℝ CountableEllOne)} (hK : IsCompact K) :
    Continuous (fun x : K => (toWeakSpace ℝ CountableEllOne).symm x.val) := by
  letI : FirstCountableTopology K := weakEllOne_compact_firstCountable hK
  apply SeqContinuous.continuous
  intro u x hu
  let v : ℕ → CountableEllOne := fun n =>
    (toWeakSpace ℝ CountableEllOne).symm (u n).val - (toWeakSpace ℝ CountableEllOne).symm x.val
  have hv : ∀ φ : CountableEllOne →L[ℝ] ℝ, Tendsto (fun n => φ (v n)) atTop (𝓝 0) := by
    intro φ
    have hφ : Continuous (fun y : K => φ ((toWeakSpace ℝ CountableEllOne).symm y.val)) :=
      (WeakBilin.eval_continuous (topDualPairing ℝ CountableEllOne).flip φ).comp continuous_subtype_val
    have ht := ((hφ.tendsto x).comp hu).sub
      (tendsto_const_nhds (x := φ ((toWeakSpace ℝ CountableEllOne).symm x.val)))
    simpa only [v, map_sub, sub_self] using ht
  have ht := (ellOne_schur v hv).add
    (tendsto_const_nhds (x := (toWeakSpace ℝ CountableEllOne).symm x.val))
  simpa only [v, sub_add_cancel, zero_add] using ht

theorem isCompact_norm_of_weakEllOne
    {K : Set (WeakSpace ℝ CountableEllOne)} (hK : IsCompact K) :
    IsCompact ((toWeakSpace ℝ CountableEllOne).symm '' K) :=
  hK.image_of_continuousOn
    (continuousOn_iff_continuous_restrict.mpr (weakEllOne_compact_norm_continuous hK))

theorem isCompact_ellOne_uniform_coordinates
    {K : Set CountableEllOne} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x ∈ K, ∀ n ≥ N, ‖x n‖ < ε := by
  obtain ⟨F, _, hF, hcover⟩ := hK.finite_cover_balls (half_pos hε)
  have he : ∀ᶠ n : ℕ in atTop, ∀ x ∈ F, ‖x n‖ < ε / 2 := by
    apply hF.eventually_all.mpr
    intro x _
    exact ((lp_one_hasSum_norm x).summable.tendsto_atTop_zero).eventually
      (gt_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun x hx n hn => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - y‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxy
  have hcoord : ‖x n - y n‖ ≤ ‖x - y‖ :=
    lp.norm_apply_le_norm (by norm_num) (x - y) n
  have htri := norm_add_le (x n - y n) (y n)
  rw [sub_add_cancel] at htri
  linarith [hN n hn y hy]

end ThesisCommon
