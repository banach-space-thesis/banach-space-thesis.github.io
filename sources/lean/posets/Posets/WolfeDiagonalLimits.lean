import Posets.WolfeOutsideMass

/-! Signed diagonal lower bounds pass from the bottom of a clopen tower to
weak-star limits once the outside mass is small. Taking real parts makes the
same two-colour argument valid over real and complex scalars. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeDiagonalLimitsDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeDiagonalLimitsDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfe_norm_indicator_sub_le (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U G : Set K}
    (hU : IsClopen U) (hcU : IsCompact U) (hG : IsClopen G) (hcG : IsCompact G)
    (hUG : U ⊆ G) :
    ‖μ (JLMS.clopenIndicator G hG hcG) - μ (JLMS.clopenIndicator U hU hcU)‖ ≤
      wolfeMass M μ (G \ U) := by
  classical
  let f : JLMS.CZero 𝕜 K := JLMS.clopenIndicator G hG hcG - JLMS.clopenIndicator U hU hcU
  have heval (x : K) : f x = (if x ∈ G then 1 else 0) - (if x ∈ U then 1 else 0) := by
    change JLMS.evaluation x f = _
    simp only [f, map_sub, JLMS.evaluation_apply, JLMS.clopenIndicator_apply]
  have hs : Function.support f ⊆ G \ U := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact False.elim (hx (by simp [heval, hxU, hUG hxU]))
    · refine ⟨?_, hxU⟩
      by_contra hxG
      exact hx (by simp [heval, hxU, hxG])
  have hn : ‖f‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro x
    change ‖f x‖ ≤ 1
    by_cases hxU : x ∈ U
    · simp [heval, hxU, hUG hxU]
    · by_cases hxG : x ∈ G <;> simp [heval, hxU, hxG]
  simpa only [f, map_sub] using norm_apply_le_wolfeMass_of_support_subset M μ f hs hn

theorem wolfe_re_indicator_le_of_outside (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {U G H : Set K}
    (hU : IsClopen U) (hcU : IsCompact U) (hG : IsClopen G) (hcG : IsCompact G)
    (hUG : U ⊆ G) (hGH : G ⊆ H) {ell ε : ℝ}
    (hdiag : ell ≤ RCLike.re (μ (JLMS.clopenIndicator U hU hcU)))
    (houtside : wolfeMass M μ (H \ U) ≤ ε) :
    ell - ε ≤ RCLike.re (μ (JLMS.clopenIndicator G hG hcG)) := by
  have hn := (wolfe_norm_indicator_sub_le M μ hU hcU hG hcG hUG).trans
    ((wolfeMass_mono M μ (diff_subset_diff_left hGH)).trans houtside)
  have hr := RCLike.re_le_norm
    (μ (JLMS.clopenIndicator U hU hcU) - μ (JLMS.clopenIndicator G hG hcG))
  rw [map_sub, norm_sub_rev] at hr
  linarith

theorem wolfe_re_indicator_lower_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (M : JLMS.AtomicDualModel 𝕜 K)
    {μ : ι → WeakDual 𝕜 (JLMS.CZero 𝕜 K)}
    {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hμ : Tendsto μ l (𝓝 ν))
    (U : ι → Set K) (hU : ∀ i, IsClopen (U i)) (hcU : ∀ i, IsCompact (U i))
    {G H : Set K} (hG : IsClopen G) (hcG : IsCompact G)
    (hUG : ∀ i, U i ⊆ G) (hGH : G ⊆ H) {ell ε : ℝ}
    (hdiag : ∀ᶠ i in l, ell ≤ RCLike.re (μ i (JLMS.clopenIndicator (U i) (hU i) (hcU i))))
    (houtside : ∀ᶠ i in l, wolfeMass M (μ i) (H \ U i) ≤ ε) :
    ell - ε ≤ RCLike.re (ν (JLMS.clopenIndicator G hG hcG)) := by
  have ht := RCLike.continuous_re.continuousAt.tendsto.comp
    ((WeakDual.eval_continuous (JLMS.clopenIndicator G hG hcG)).continuousAt.tendsto.comp hμ)
  apply ge_of_tendsto ht
  filter_upwards [hdiag, houtside] with i hi ho
  exact wolfe_re_indicator_le_of_outside M (μ i) (hU i) (hcU i) hG hcG
    (hUG i) hGH hi ho

end Posets
