import ThesisCommon.Analysis.IntervalLocalizationAssembly
import ThesisCommon.Analysis.MilutinCantorExtension

/-! Unconditional primariness of the interval continuous-function space and
its Banach-exponent sequence sums. The base-space proof uses diagonal atoms,
Egorov selection, and a contractive Cantor extension. It is an alternative
proof route, not a formalization of the separately stated Weis bound. -/

noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem interval_cantor_factors_four
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) :
    FactorsIdentityWith T (CantorContinuous 𝕜) 4 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T)
        (CantorContinuous 𝕜) 4 := by
  apply interval_cantor_factors_four_of_contractively_extendible _ T
  intro e he
  exact ⟨milutinCantorExtend e he, norm_milutinCantorExtend_le e he,
    milutinCantorExtend_on_image e he⟩

theorem interval_hasCPFP_four : HasCPFP 𝕜 (IntervalContinuous 𝕜) 4 := by
  apply interval_hasCPFP_four_of_cantor_extension
  intro e he
  exact ⟨milutinCantorExtend e he, norm_milutinCantorExtend_le e he,
    milutinCantorExtend_on_image e he⟩

theorem interval_hasUPFP : HasUPFP 𝕜 (IntervalContinuous 𝕜) :=
  ⟨4, by norm_num, interval_hasCPFP_four⟩

theorem interval_primary : IsPrimary 𝕜 (IntervalContinuous 𝕜) :=
  interval_hasUPFP.isPrimary_of_sequenceSelfSimilar interval_sequenceSelfSimilar

theorem interval_cZero_upfp_primary :
    HasUPFP 𝕜 (CZeroSum (IntervalContinuous 𝕜)) ∧
      IsPrimary 𝕜 (CZeroSum (IntervalContinuous 𝕜)) := by
  have h := interval_hasUPFP.of_equiv (intervalCZeroEquiv (𝕜 := 𝕜))
  exact ⟨h, h.cZero_isPrimary⟩

theorem interval_sequence_upfp_primary (p : BanachExponent) :
    HasUPFP 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) ∧
      IsPrimary 𝕜 (SequenceSum p (IntervalContinuous 𝕜)) :=
  interval_lp_upfp_primary interval_hasUPFP intervalCZeroEquiv p.val

theorem interval_lp_unconditional_upfp_primary (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) ∧
      IsPrimary 𝕜 (lp (fun _ : ℕ => IntervalContinuous 𝕜) p) :=
  interval_lp_upfp_primary interval_hasUPFP intervalCZeroEquiv p

end ThesisCommon
