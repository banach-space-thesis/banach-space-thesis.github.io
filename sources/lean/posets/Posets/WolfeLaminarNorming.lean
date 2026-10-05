import Posets.WolfeOutsideMass
import Mathlib.Order.Preorder.Finite

/-! Quantitative norming for the clopen laminar families used in the
countable-ordinal primariness proof. The estimates use absolute values and
therefore work over both real and complex scalars. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

local instance wolfeLaminarNormingDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeLaminarNormingDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfe_norm_apply_le_two_mass
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (f : JLMS.CZero 𝕜 K) (U V : Set K) {C D : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ U.indicator (fun _ => C) x + V.indicator (fun _ => D) x) :
    ‖μ f‖ ≤ C * wolfeMass M μ U + D * wolfeMass M μ V := by
  classical
  let a := M.representation (WeakDual.toStrongDual μ)
  have hu : HasSum (fun x => U.indicator (fun x => ‖a x‖) x) (wolfeMass M μ U) := by
    rw [wolfeMass_eq_tsum]
    exact ((JLMS.ellOneOn_summable_norm a).indicator U).hasSum
  have hv : HasSum (fun x => V.indicator (fun x => ‖a x‖) x) (wolfeMass M μ V) := by
    rw [wolfeMass_eq_tsum]
    exact ((JLMS.ellOneOn_summable_norm a).indicator V).hasSum
  apply (JLMS.atomicDual_apply_hasSum M (WeakDual.toStrongDual μ) f).norm_le_of_bounded
    ((hu.mul_left C).add (hv.mul_left D))
  intro x
  change ‖a x * f x‖ ≤ _
  rw [norm_mul]
  have hx := mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg (a x))
  by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
    simpa [hxU, hxV, mul_add, add_mul, mul_comm] using hx

theorem wolfe_norm_sub_indicator_le
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (f : JLMS.CZero 𝕜 K) {H G E : Set K} (hG : IsClopen G) (hcG : IsCompact G)
    (hGH : G ⊆ H) (hs : Function.support f ⊆ H) (a : 𝕜) (ha : ‖a‖ ≤ ‖f‖)
    (hconst : ∀ x ∈ G \ E, f x = a) :
    ‖μ f - a * μ (JLMS.clopenIndicator G hG hcG)‖ ≤
      ‖f‖ * wolfeMass M μ (H \ G) + (2 * ‖f‖) * wolfeMass M μ E := by
  classical
  have hb (x : K) : ‖(f - a • JLMS.clopenIndicator (𝕜 := 𝕜) G hG hcG : JLMS.CZero 𝕜 K) x‖ ≤
      (H \ G).indicator (fun _ => ‖f‖) x + E.indicator (fun _ => 2 * ‖f‖) x := by
    change ‖f x - a * JLMS.clopenIndicator G hG hcG x‖ ≤ _
    rw [JLMS.clopenIndicator_apply]
    by_cases hxH : x ∈ H
    · by_cases hxG : x ∈ G
      · by_cases hxE : x ∈ E
        · simp only [hxG, if_true, mul_one]
          have hn := norm_sub_le (f x) a
          have hf := JLMS.norm_CZero_apply_le f x
          rw [indicator_of_notMem (show x ∉ H \ G from fun h => h.2 hxG),
            indicator_of_mem hxE]
          linarith
        · simp [hxG, hxE, hconst x ⟨hxG, hxE⟩]
      · have hn := JLMS.norm_CZero_apply_le f x
        by_cases hxE : x ∈ E <;> simp [hxH, hxG, hxE] <;> linarith [norm_nonneg f]
    · have hfx : f x = 0 := by by_contra hn; exact hxH (hs hn)
      have hxG : x ∉ G := fun h => hxH (hGH h)
      by_cases hxE : x ∈ E <;> simp [hxH, hxG, hxE, hfx, norm_nonneg f]
  have h := wolfe_norm_apply_le_two_mass M μ (f - a • JLMS.clopenIndicator G hG hcG)
    (H \ G) E hb
  simpa only [map_sub, map_smul, smul_eq_mul] using h

theorem wolfe_norming_of_small_exceptions
    (M : JLMS.AtomicDualModel 𝕜 K) (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (f : JLMS.CZero 𝕜 K) {H G E : Set K} (hG : IsClopen G) (hcG : IsCompact G)
    (hGH : G ⊆ H) (hs : Function.support f ⊆ H) (a : 𝕜) (ha : ‖a‖ = ‖f‖)
    (hconst : ∀ x ∈ G \ E, f x = a) {ell η : ℝ}
    (hell : ell ≤ ‖μ (JLMS.clopenIndicator G hG hcG)‖)
    (houtside : wolfeMass M μ (H \ G) ≤ η) (hchildren : wolfeMass M μ E ≤ η) :
    (ell - 3 * η) * ‖f‖ ≤ ‖μ f‖ := by
  have h := wolfe_norm_sub_indicator_le M μ f hG hcG hGH hs a ha.le hconst
  have hlower := norm_le_norm_sub_add (a * μ (JLMS.clopenIndicator G hG hcG)) (μ f)
  rw [norm_mul, ha, norm_sub_rev] at hlower
  have hmul := mul_le_mul_of_nonneg_left hell (norm_nonneg f)
  have ho := mul_le_mul_of_nonneg_left houtside (norm_nonneg f)
  have hc := mul_le_mul_of_nonneg_left hchildren (show 0 ≤ 2 * ‖f‖ by positivity)
  nlinarith

end Posets
