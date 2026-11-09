import PL1CD.Variation
import PL1.TruncatedResolventFactorization
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology NNReal

namespace PL1CD.Variation

variable (𝕜 : Type*) [RCLike 𝕜]

theorem resolvent_vanishing_of_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hnoise : ∀ (ε : ℝ≥0), 0 < ε → ∀ B : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜,
      averagedVariation 𝕜 (HaarL1 𝕜) M N H hH
        ((PL1.Noise.noiseL1 𝕜 rates ε).comp B) = 0)
    (t : PL1.Noise.PositiveTime) (B : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) :
    averagedVariation 𝕜 (HaarL1 𝕜) M N H hH
      ((PL1.Noise.resolventL1 𝕜 rates t).comp B) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) := by
    simpa [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have ht := PL1.Noise.truncatedResolventL1_tendsto 𝕜 rates atTop t ε hεlim
  have hcomp : Tendsto
      (fun n => (PL1.Noise.truncatedResolventL1 𝕜 rates t (ε n)).comp B) atTop
      (𝓝 ((PL1.Noise.resolventL1 𝕜 rates t).comp B)) :=
    ((continuous_id.clm_comp (continuous_const : Continuous
      (fun _ : (HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) => B))).tendsto _).comp ht
  have hp := ((averagedVariation_continuous 𝕜 (HaarL1 𝕜) M N H hH).tendsto _).comp hcomp
  have hzero (n : ℕ) :
      averagedVariation 𝕜 (HaarL1 𝕜) M N H hH
        ((PL1.Noise.truncatedResolventL1 𝕜 rates t (ε n)).comp B) = 0 := by
    rw [PL1.Noise.truncatedResolventL1_eq_noise_comp_resolvent]
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc, map_smul_eq_mul,
      hnoise (ε n) (hε n) ((PL1.Noise.resolventL1 𝕜 rates t).comp B), mul_zero]
  exact tendsto_nhds_unique hp (by simpa only [Function.comp_def, hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end PL1CD.Variation
