import PL1CD.AbsoluteMajorant
import PL1CD.SemigroupVanishing

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace PL1CD.Variation
open PL1.Walsh PL1CD.PositiveHaarOperators

theorem endpoint_tendsto_zero_of_averagedVariation_eq_zero
    {𝕜 Z : Type*} [RCLike 𝕜] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (T : Variation.HaarL1 𝕜 →L[𝕜] Z)
    (hz : averagedVariation 𝕜 Z M N H hH T = 0) :
    Tendsto (fun s => endpointSeminorm 𝕜 Z M N s T) (atTop ⊓ 𝓟 H) (𝓝 0) := by
  let := alongInfinite_neBot hH
  let p := endpointSeminorm 𝕜 Z M N
  have hu := PL1CD.seminormSequence_boundedAbove p 2 (endpointSeminorm_le 𝕜 Z M N)
    (atTop ⊓ 𝓟 H) T
  have hl := PL1CD.seminormSequence_boundedBelow p (atTop ⊓ 𝓟 H) T
  have hinf : 0 ≤ liminf (fun s => p s T) (atTop ⊓ 𝓟 H) :=
    le_liminf_of_le hu.isCoboundedUnder_ge (Eventually.of_forall (fun s => apply_nonneg (p s) T))
  have hsup : limsup (fun s => p s T) (atTop ⊓ 𝓟 H) ≤ 0 := by
    change averagedVariation 𝕜 Z M N H hH T ≤ 0
    exact hz.le
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hu hl

theorem real_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (u : ℝ≥0) (hu : 0 < u) (B : Variation.HaarL1 ℝ →L[ℝ] Variation.HaarL1 ℝ) :
    averagedVariation ℝ (Variation.HaarL1 ℝ) M N H hH
      ((PL1.Noise.noiseL1 ℝ rates u).comp B) = 0 := by
  obtain ⟨P, Q, hP, hQ, hB⟩ := HaarPartitions.exists_positive_decomposition B
  rw [hB, ContinuousLinearMap.comp_sub]
  apply le_antisymm _ (apply_nonneg _ _)
  exact (map_sub_le_add _ _ _).trans (by
    rw [positive_noise_vanishing rates M N H hH hgrowth u hu P hP,
      positive_noise_vanishing rates M N H hH hgrowth u hu Q hQ]
    simp)

theorem real_resolvent_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (t : PL1.Noise.PositiveTime) (B : Variation.HaarL1 ℝ →L[ℝ] Variation.HaarL1 ℝ) :
    averagedVariation ℝ (Variation.HaarL1 ℝ) M N H hH
      ((PL1.Noise.resolventL1 ℝ rates t).comp B) = 0 :=
  resolvent_vanishing_of_noise_vanishing ℝ rates M N H hH
    (fun u hu B => real_noise_vanishing rates M N H hH hgrowth u hu B) t B

end PL1CD.Variation
