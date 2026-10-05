import ThesisCommon.Analysis.GowersMaureyFiniteNorming
import ThesisCommon.Analysis.GowersMaureyBlockImageTails
import ThesisCommon.Analysis.GowersMaureyTailFunctionalBounds

/-! Near norming by genuine finite dual-unit functionals after a prescribed
cutoff. The completed operator images need not have finite support. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_finite_tail_near_norming (D : ConstructionData 𝕜)
    (x : ShiftSpace D) (K : ℕ) {δ : ℝ} (_hδ : 0 < δ)
    (hx : ‖initialSum D (K+1) x‖ < δ) :
    ∃ a : C00 𝕜, a ∈ afterCutoff K ∧ DualUnit (implicitNorm D) a ∧
      ‖x‖ - 2*δ < RCLike.re (completedPairing D a x) := by
  classical
  obtain ⟨y,hyK,hy⟩ := exists_finite_after_approx_of_initialSum_small D x K hx
  let E : Interval := ⟨K+1, y.support.sup id⟩
  have hyE : y.support ⊆ E.set := by
    intro n hn
    apply Finset.mem_Icc.mpr
    refine ⟨?_,Finset.le_sup (f := id) hn⟩
    have hne := Finsupp.mem_support_iff.mp hn
    change K+1 ≤ n
    by_contra h
    exact hne (hyK n (by omega))
  obtain ⟨a,haE,hau,ha⟩ := exists_finite_interval_norming D E y
  have haK : a ∈ afterCutoff K := by
    intro n hn
    apply Finsupp.notMem_support_iff.mp
    intro hna
    have hh := (Finset.mem_Icc.mp (haE hna)).1
    change K+1 ≤ n at hh
    omega
  have hae : completedPairing D a (denseEmbedding D y) = (implicitNorm D y : 𝕜) := by
    rw [completedPairing_denseEmbedding, ha, restrict_eq_self_of_support_subset hyE]
  have herror : ‖completedPairing D a (x-denseEmbedding D y)‖ < δ :=
    (completedPairing_norm_bound hau _).trans_lt hy
  have hre := RCLike.re_le_norm (completedPairing D a (denseEmbedding D y-x))
  rw [map_sub,hae,map_sub,RCLike.ofReal_re,norm_sub_rev] at hre
  have herror' : ‖completedPairing D a x - (implicitNorm D y : 𝕜)‖ < δ := by
    simpa only [map_sub,hae] using herror
  have hnorm := norm_sub_norm_le x (denseEmbedding D y)
  rw [denseEmbedding_norm,PreSpace.norm_def] at hnorm
  change ‖x‖ - implicitNorm D y ≤ ‖x-denseEmbedding D y‖ at hnorm
  refine ⟨a,haK,hau,?_⟩
  linarith

theorem BlockTestSequence.eventually_finite_tail_near_norming
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (T : Y →L[𝕜] ShiftSpace D)
    (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ a : C00 𝕜,
      a ∈ afterCutoff K ∧ DualUnit (implicitNorm D) a ∧
      ‖T (u.inSubspace n)‖ - 2*δ <
        RCLike.re (completedPairing D a (T (u.inSubspace n))) := by
  have hh := (u.tendsto_initialSum_operator_zero T (K+1)).norm.eventually_lt_const
    (by simpa only [norm_zero] using hδ)
  filter_upwards [hh] with n hn
  exact exists_finite_tail_near_norming D _ K hδ hn

end ThesisCommon.GowersMaurey
