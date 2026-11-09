import PL1CD.PositiveHaarOperators
import PL1CD.EntropyGrowth
import PL1CD.StageBlocks

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace PL1CD.PositiveHaarOperators
open PL1.Walsh PL1CD.Entropy PL1CD.CylinderRefinement

theorem bounded_positive_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N d : ℕ → ℕ) (a : ℕ → ℝ≥0)
    (H : Set ℕ) (hH : H.Infinite) (hMmono : Monotone M)
    (hNtop : Tendsto N atTop atTop)
    (hrates : ∀ᶠ s in atTop ⊓ 𝓟 H, ∀ j, d s ≤ j → (a s : ℝ) ≤ rates j)
    (hd : Tendsto (fun s => (d s : ℝ) / N s) (atTop ⊓ 𝓟 H) (𝓝 0))
    (hMN : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun s => ((M (N s) : ℝ) / N s) * Real.exp (-ε * a s))
      (atTop ⊓ 𝓟 H) (𝓝 0))
    (u : ℝ≥0) (hu : 0 < u)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1)
    (b : ℝ) (hb : 1 ≤ b) (hbound : ∀ᵐ x ∂haar, B oneL1 x ≤ b) :
    PL1CD.Variation.averagedVariation ℝ HaarL1 M N H hH
      ((PL1.Noise.noiseL1 ℝ rates u).comp B) = 0 := by
  let D := (PL1.Noise.noiseL1 ℝ rates u).comp B
  let entropy := levelEntropy D M
  have hstep := noise_level_energy rates u B hB hcontract b hb hbound M hMmono
  have hN : ∀ᶠ s in atTop ⊓ 𝓟 H, 0 < N s :=
    (hNtop.eventually (eventually_gt_atTop 0)).filter_mono inf_le_left
  have hinv : Tendsto (fun s => (N s : ℝ)⁻¹) (atTop ⊓ 𝓟 H) (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNtop)).mono_left inf_le_left
  apply PL1CD.Variation.averagedVariation_eq_zero_of_entropy ℝ HaarL1
    M N H hH D entropy hstep hN
  apply EntropyEnergy.entropy_growth_tendsto_zero
    (fun n => PL1CD.Variation.levelSeminorm ℝ HaarL1 M n D)
    entropy M N d (fun s => (a s : ℝ)) (atTop ⊓ 𝓟 H)
    (u : ℝ) (Real.log b + 1) u.coe_nonneg (fun s => (a s).coe_nonneg)
    hstep hN _ hd (hMN u (by exact_mod_cast hu)) hinv
  filter_upwards [hrates] with s hs
  simpa only [entropy, D, add_assoc] using
    noise_level_entropy_le rates u (a s) (d s) hs B hB hcontract b hb hbound M (N s)

theorem bounded_positive_stage_noise_vanishing
    (A H : Set ℕ) (hH : H.Infinite) (hHA : (H ∩ A).Finite)
    (u : ℝ≥0) (hu : 0 < u)
    (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1)
    (b : ℝ) (hb : 1 ≤ b) (hbound : ∀ᵐ x ∂haar, B oneL1 x ≤ b) :
    PL1CD.Variation.averagedVariation ℝ HaarL1
      StageParameters.filtration StageParameters.levels H hH
      ((PL1.Noise.noiseL1 ℝ (StageParameters.rates A) u).comp B) = 0 := by
  apply bounded_positive_noise_vanishing (StageParameters.rates A)
    StageParameters.filtration StageParameters.levels
    (fun s => StageParameters.dimension (s - 1))
    (fun s => (StageParameters.high s : ℝ≥0)) H hH
    StageParameters.filtration_strictMono.monotone
    StageParameters.levels_strictMono.tendsto_atTop
    _ (StageParameters.previous_dimension_ratio_tendsto.mono_left inf_le_left)
    _ u hu B hB hcontract b hb hbound
  · have hf : ∀ᶠ s in atTop, s ∉ H ∩ A := by
      simpa only [Nat.cofinite_eq_atTop] using hHA.eventually_cofinite_notMem
    filter_upwards [hf.filter_mono inf_le_left,
      (eventually_gt_atTop 0).filter_mono (inf_le_left : atTop ⊓ 𝓟 H ≤ atTop),
      (show ∀ᶠ s in atTop ⊓ 𝓟 H, s ∈ H from
        (show ∀ᶠ s in 𝓟 H, s ∈ H from mem_principal_self H).filter_mono inf_le_right)]
      with s hs hpos hsH
    intro j hj
    exact_mod_cast StageParameters.high_le_rates_after hpos A
      (fun hsA => hs ⟨hsH, hsA⟩) hj
  · intro ε hε
    simpa only [StageParameters.filtration_levels, NNReal.coe_natCast] using
      (StageParameters.dimension_ratio_times_exp_high_tendsto hε).mono_left inf_le_left

end PL1CD.PositiveHaarOperators
