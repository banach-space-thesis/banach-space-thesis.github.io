import PL1CD.PositiveVanishing

noncomputable section
open Filter
open scoped Topology NNReal

namespace PL1CD
open PositiveHaarOperators

theorem stage_growthCriterion (A H : Set ℕ) (hHA : (H ∩ A).Finite) :
    GrowthCriterion (StageParameters.rates A)
      StageParameters.filtration StageParameters.levels H := by
  refine ⟨StageParameters.filtration_strictMono.monotone,
    StageParameters.levels_strictMono.tendsto_atTop,
    fun s => StageParameters.dimension (s - 1),
    fun s => (StageParameters.high s : ℝ≥0), ?_,
    StageParameters.previous_dimension_ratio_tendsto.mono_left inf_le_left, ?_⟩
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

end PL1CD
