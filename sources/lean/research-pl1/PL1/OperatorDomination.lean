import PL1.IntervalDyadicApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Domination and target truncation for operators out of interval L1 -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PL1.OperatorDomination

attribute [local instance] DyadicTrace.intervalMeasure_probability

variable {𝕜 Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω] (μ : Measure Ω)

def restriction (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ) :
    Lp 𝕜 ∞ intervalMeasure →L[𝕜] Lp 𝕜 1 μ :=
  B.comp (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top)

theorem exists_measurable_dominator (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ) :
    ∃ G : Ω → ℝ, Measurable G ∧ Integrable G μ ∧ (∀ x, 0 ≤ G x) ∧
      (∫ x, G x ∂μ) ≤ ‖B‖ ∧ ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
        ∀ᵐ x ∂μ, ‖restriction μ B f x‖ ≤ G x := by
  obtain ⟨g, hg, hgpos, hgint, hgdom⟩ := DyadicTrace.exists_integrable_dominator μ B
  let G : Ω → ℝ := fun x => max 0 (hg.aestronglyMeasurable.mk g x)
  have hGmeas : Measurable G := measurable_const.max hg.aestronglyMeasurable.measurable_mk
  have hGae : g =ᵐ[μ] G := by
    filter_upwards [hg.aestronglyMeasurable.ae_eq_mk] with x hx
    change g x = max 0 (hg.aestronglyMeasurable.mk g x)
    rw [← hx, max_eq_right (hgpos x)]
  refine ⟨G, hGmeas, hg.congr hGae, fun x => le_max_left _ _, ?_, ?_⟩
  · rw [← integral_congr_ae hGae]
    exact hgint
  · intro f hf
    filter_upwards [hgdom f hf, hGae] with x hx hxx
    exact hx.trans_eq hxx

theorem norm_mask_restriction_le (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (G : Ω → ℝ) (hG : Integrable G μ) (hGpos : ∀ x, 0 ≤ G x)
    (hdom : ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
      ∀ᵐ x ∂μ, ‖restriction μ B f x‖ ≤ G x)
    (A : Set Ω) (hA : MeasurableSet A) :
    ‖(L1Masks.mask μ A hA).comp (restriction μ B)‖ ≤ ∫ x in A, G x ∂μ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (integral_nonneg hGpos)
  intro f hf
  change ‖L1Masks.mask μ A hA (restriction μ B f)‖ ≤ _
  rw [L1Masks.norm_mask]
  exact integral_mono_ae (L1.integrable_coeFn (restriction μ B f)).norm.integrableOn
    hG.integrableOn (ae_restrict_of_ae (hdom f hf.le))

theorem mask_compl (A : Set Ω) (hA : MeasurableSet A) :
    ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) - L1Masks.mask μ A hA =
      L1Masks.mask μ Aᶜ hA.compl := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  change (f - L1Masks.mask μ A hA f : Lp 𝕜 1 μ) =ᵐ[μ] L1Masks.mask μ Aᶜ hA.compl f
  filter_upwards [Lp.coeFn_sub f (L1Masks.mask μ A hA f),
    L1Masks.coeFn_mask μ A hA f, L1Masks.coeFn_mask μ Aᶜ hA.compl f] with x hs ha hc
  rw [hs, Pi.sub_apply, ha, hc]
  by_cases hx : x ∈ A <;> simp [hx]

theorem integral_upper_tail_tendsto_zero (G : Ω → ℝ)
    (hGmeas : Measurable G) (hG : Integrable G μ) (hGpos : ∀ x, 0 ≤ G x) :
    Tendsto (fun n : ℕ => ∫ x in {x | (n : ℝ) < G x}, G x ∂μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : MeasurableSet {x | (n : ℝ) < G x} := measurableSet_lt measurable_const hGmeas
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0 : ℝ)) G
    (fun n => (hGmeas.indicator (hm n)).aestronglyMeasurable) hG
    (fun n => ae_of_all _ (fun x => by
      by_cases hx : (n : ℝ) < G x
      · rw [Set.indicator_of_mem (show x ∈ {x | (n : ℝ) < G x} from hx)]
        simp only [Real.norm_eq_abs, abs_of_nonneg (hGpos x), le_refl]
      · rw [Set.indicator_of_notMem (show x ∉ {x | (n : ℝ) < G x} from hx), norm_zero]
        exact hGpos x))
    (ae_of_all _ (fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt (G x)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : G x ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
      exact (Set.indicator_of_notMem
        (show x ∉ {x | (n : ℝ) < G x} from not_lt.mpr hle) G).symm))
  simpa only [integral_indicator (hm _), integral_zero] using ht

theorem norm_cutoff_error_le (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (G : Ω → ℝ) (hGmeas : Measurable G) (hG : Integrable G μ) (hGpos : ∀ x, 0 ≤ G x)
    (hdom : ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
      ∀ᵐ x ∂μ, ‖restriction μ B f x‖ ≤ G x) (M : ℝ) :
    ‖restriction μ (B - (L1Masks.mask μ {x | G x ≤ M}
      (measurableSet_le hGmeas measurable_const)).comp B)‖ ≤
      ∫ x in {x | M < G x}, G x ∂μ := by
  have hset : {x | G x ≤ M}ᶜ = {x | M < G x} := by ext x; simp
  have heq : B - (L1Masks.mask μ {x | G x ≤ M}
      (measurableSet_le hGmeas measurable_const)).comp B =
      (L1Masks.mask μ {x | M < G x} (measurableSet_lt measurable_const hGmeas)).comp B := by
    calc
      _ = (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) - L1Masks.mask μ {x | G x ≤ M}
          (measurableSet_le hGmeas measurable_const)).comp B := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
      _ = _ := by rw [mask_compl]; simp only [hset]
  rw [heq]
  simpa only [restriction, ContinuousLinearMap.comp_assoc] using
    norm_mask_restriction_le μ B G hG hGpos hdom {x | M < G x}
      (measurableSet_lt measurable_const hGmeas)

theorem cutoff_approximation (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ)
    (G : Ω → ℝ) (hGmeas : Measurable G) (hG : Integrable G μ) (hGpos : ∀ x, 0 ≤ G x)
    (hdom : ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
      ∀ᵐ x ∂μ, ‖restriction μ B f x‖ ≤ G x) :
    Tendsto (fun n : ℕ => ‖restriction μ (B - (L1Masks.mask μ {x | G x ≤ (n : ℝ)}
      (measurableSet_le hGmeas measurable_const)).comp B)‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    norm_cutoff_error_le μ B G hGmeas hG hGpos hdom n)
    (integral_upper_tail_tendsto_zero μ G hGmeas hG hGpos)

end PL1.OperatorDomination
