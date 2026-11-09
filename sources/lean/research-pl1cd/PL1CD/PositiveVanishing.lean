import PL1CD.BoundedPositiveVanishing
import PL1CD.PositiveTruncation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace PL1CD.PositiveHaarOperators
open PL1.Walsh PL1CD.Variation

structure GrowthCriterion (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) : Prop where
  monotone : Monotone M
  endpoints : Tendsto N atTop atTop
  exists_parameters : ∃ (d : ℕ → ℕ) (a : ℕ → ℝ≥0),
    (∀ᶠ s in atTop ⊓ 𝓟 H, ∀ j, d s ≤ j → (a s : ℝ) ≤ rates j) ∧
    Tendsto (fun s => (d s : ℝ) / N s) (atTop ⊓ 𝓟 H) (𝓝 0) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun s => ((M (N s) : ℝ) / N s) * Real.exp (-ε * a s))
      (atTop ⊓ 𝓟 H) (𝓝 0)

theorem averagedVariation_le_of_level_bound
    (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (B : HaarL1 →L[ℝ] HaarL1) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, levelSeminorm ℝ HaarL1 M n B ≤ C) :
    averagedVariation ℝ HaarL1 M N H hH B ≤ C := by
  letI := alongInfinite_neBot hH
  change limsup (fun s => endpointSeminorm ℝ HaarL1 M N s B) (atTop ⊓ 𝓟 H) ≤ C
  apply limsup_le_of_le (PL1CD.seminormSequence_cobounded _ _ _) (Eventually.of_forall _)
  intro s
  rw [endpointSeminorm, averageSeminorm_apply]
  by_cases hz : N s = 0
  · simpa [hz] using hC
  · have hn : (N s : ℝ) ≠ 0 := by exact_mod_cast hz
    calc
      _ ≤ (N s : ℝ)⁻¹ * ∑ _n ∈ Finset.range (N s), C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hbound n)) (by positivity)
      _ = C := by simp [hn]

theorem IsPositive.smul {B : HaarL1 →L[ℝ] HaarL1} (hB : IsPositive B)
    (c : ℝ) (hc : 0 ≤ c) : IsPositive (c • B) := by
  intro f hf
  filter_upwards [hB f hf, Lp.coeFn_smul c (B f)] with x hx he
  change 0 ≤ (c • B f) x
  rw [he, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg hc hx

theorem positive_contractive_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (u : ℝ≥0) (hu : 0 < u) (B : HaarL1 →L[ℝ] HaarL1)
    (hB : IsPositive B) (hcontract : ‖B‖ ≤ 1) :
    averagedVariation ℝ HaarL1 M N H hH ((PL1.Noise.noiseL1 ℝ rates u).comp B) = 0 := by
  obtain ⟨d, a, hr, hd, hMN⟩ := hgrowth.exists_parameters
  let p := averagedVariation ℝ HaarL1 M N H hH
  have hp (n : ℕ) : p ((PL1.Noise.noiseL1 ℝ rates u).comp B) ≤
      2 * ‖tail B (2 * (n : ℝ) + 2) oneL1‖ := by
    let b : ℝ := 2 * (n : ℝ) + 2
    have hb : 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hcut : p ((PL1.Noise.noiseL1 ℝ rates u).comp (cutoff B b)) = 0 :=
      bounded_positive_noise_vanishing rates M N d a H hH hgrowth.monotone hgrowth.endpoints
        hr hd hMN u hu (cutoff B b) (cutoff_positive B hB b)
        ((norm_cutoff_le B b).trans hcontract) b hb (cutoff_one_bound B b (by linarith))
    have htail := averagedVariation_le_of_level_bound M N H hH
      ((PL1.Noise.noiseL1 ℝ rates u).comp (tail B b))
      (2 * ‖tail B b oneL1‖) (by positivity)
      (positive_noise_level_bound rates u (tail B b) (tail_positive B hB b) M hgrowth.monotone)
    have he : (PL1.Noise.noiseL1 ℝ rates u).comp B =
        (PL1.Noise.noiseL1 ℝ rates u).comp (cutoff B b) +
        (PL1.Noise.noiseL1 ℝ rates u).comp (tail B b) := by
      rw [← ContinuousLinearMap.comp_add, cutoff_add_tail]
    rw [he]
    exact (map_add_le_add p _ _).trans (by simpa only [hcut, zero_add] using htail)
  apply le_antisymm _ (apply_nonneg _ _)
  apply ge_of_tendsto (by simpa only [mul_zero] using
    (tail_one_norm_tendsto_zero B).const_mul 2)
  exact Eventually.of_forall hp

theorem positive_noise_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (u : ℝ≥0) (hu : 0 < u) (B : HaarL1 →L[ℝ] HaarL1) (hB : IsPositive B) :
    averagedVariation ℝ HaarL1 M N H hH ((PL1.Noise.noiseL1 ℝ rates u).comp B) = 0 := by
  let c : ℝ := (‖B‖ + 1)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hnorm : ‖c • B‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
    dsimp [c]
    rw [inv_mul_eq_div]
    apply (div_le_one (by positivity : 0 < ‖B‖ + 1)).mpr
    linarith
  have hz := positive_contractive_noise_vanishing rates M N H hH hgrowth u hu
    (c • B) (hB.smul c hc.le) hnorm
  rw [ContinuousLinearMap.comp_smul, map_smul_eq_mul, Real.norm_of_nonneg hc.le] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)

end PL1CD.PositiveHaarOperators
