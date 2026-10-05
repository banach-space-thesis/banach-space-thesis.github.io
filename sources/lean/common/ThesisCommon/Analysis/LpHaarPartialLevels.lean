import ThesisCommon.Analysis.LpHaarMeanDifference

/-! Uniform control of arbitrary partial Haar levels and convergence of
successive level prefixes. No unconditional estimate across levels is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace ThesisCommon

def lpHaarPartialLevel (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p :=
  ∑ k ∈ S, (lpHaarDyadicCoefficient 𝕜 p n k).smulRight (lpHaarDyadic 𝕜 p n k)

theorem lpHaarPartialLevel_apply (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (f : IntervalLp 𝕜 p) :
    lpHaarPartialLevel 𝕜 p n S f =
      ∑ k ∈ S, lpHaarDyadicCoefficient 𝕜 p n k f • lpHaarDyadic 𝕜 p n k := by
  simp [lpHaarPartialLevel, ContinuousLinearMap.sum_apply]

theorem lpHaarPartialLevel_restrict (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarPartialLevel 𝕜 p n S f) =
      if k ∈ S then lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarLevelProjection 𝕜 p n f)
      else 0 := by
  rw [lpHaarPartialLevel_apply, map_sum]
  simp only [map_smul]
  by_cases hk : k ∈ S
  · rw [if_pos hk, lpHaarLevelProjection_restrict_parent]
    apply Finset.sum_eq_single k
    · intro j _ hjk
      rw [lpHaarDyadic_restrict_other_parent 𝕜 p n j k
        (fun h => hjk (Fin.ext h.symm)), smul_zero]
    · exact fun h => (h hk).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hkj : k.val ≠ j.val := fun h => hk ((Fin.ext h).symm ▸ hj)
    rw [lpHaarDyadic_restrict_other_parent 𝕜 p n j k hkj, smul_zero]

theorem lpHaarPartialLevel_coe_parent (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (k : Fin (2 ^ n)) (f : IntervalLp 𝕜 p) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ lpHaarCell n k →
      lpHaarPartialLevel 𝕜 p n S f x = if k ∈ S then lpHaarLevelProjection 𝕜 p n f x else 0 := by
  apply (ae_restrict_iff' (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)).mp
  have heq := lpHaarPartialLevel_restrict 𝕜 p n S k f
  by_cases hk : k ∈ S
  · rw [if_pos hk] at heq
    filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarPartialLevel 𝕜 p n S f),
      lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarLevelProjection 𝕜 p n f)] with x h₁ h₂
    rw [if_pos hk, ← h₁, heq, h₂]
  · rw [if_neg hk] at heq
    filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (lpHaarCell n k) (lpHaarPartialLevel 𝕜 p n S f),
      Lp.coeFn_zero 𝕜 p.val ((volume.restrict (Icc (0 : ℝ) 1)).restrict (lpHaarCell n k))]
      with x h₁ h₂
    rw [if_neg hk, ← h₁, heq, h₂]
    rfl

theorem lpHaarPartialLevel_norm_le (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n : ℕ)
    (S : Finset (Fin (2 ^ n))) (f : IntervalLp 𝕜 p) :
    ‖lpHaarPartialLevel 𝕜 p n S f‖ ≤ ‖lpHaarLevelProjection 𝕜 p n f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have h := ae_all_iff.mpr (fun k => lpHaarPartialLevel_coe_parent 𝕜 p n S k f)
  filter_upwards [h, lpHaarLevelCells_cover n] with x hx hcov
  obtain ⟨k, hk⟩ := mem_iUnion.mp hcov
  rw [hx k hk]
  split_ifs <;> simp

theorem lpHaarLevelProjection_tendsto_zero (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (f : IntervalLp 𝕜 p) :
    Tendsto (fun n => lpHaarLevelProjection 𝕜 p n f) atTop (𝓝 0) := by
  have h := ((lpHaarDyadicMean_tendsto 𝕜 p hp f).comp (tendsto_add_atTop_nat 1)).sub
    (lpHaarDyadicMean_tendsto 𝕜 p hp f)
  simpa only [Function.comp_apply, lpHaarDyadicMean_difference, sub_self] using h

theorem lpHaarPartialLevel_tendsto_zero (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (S : ∀ n, Finset (Fin (2 ^ n))) (f : IntervalLp 𝕜 p) :
    Tendsto (fun n => lpHaarPartialLevel 𝕜 p n (S n) f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => lpHaarPartialLevel_norm_le 𝕜 p n (S n) f)
  simpa only [norm_zero] using (lpHaarLevelProjection_tendsto_zero 𝕜 p hp f).norm

theorem lpHaar_prefixPartialSum_tendsto (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (S : ∀ n, Finset (Fin (2 ^ n))) (f : IntervalLp 𝕜 p) :
    Tendsto (fun N => lpHaarDyadicMean 𝕜 p hp 0 f +
      (∑ n ∈ Finset.range N, ∑ k : Fin (2 ^ n),
        lpHaarDyadicCoefficient 𝕜 p n k f • lpHaarDyadic 𝕜 p n k) +
      ∑ k ∈ S N, lpHaarDyadicCoefficient 𝕜 p N k f • lpHaarDyadic 𝕜 p N k) atTop (𝓝 f) := by
  have h := (lpHaar_levelPartialSum_tendsto 𝕜 p hp f).add
    (lpHaarPartialLevel_tendsto_zero 𝕜 p hp S f)
  simpa only [add_zero, lpHaarPartialLevel_apply] using h

end ThesisCommon
