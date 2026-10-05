import PFP.CountableOrdinalCoefficientProofs
import PFP.FiniteOrdinalSumProofs
import ThesisCommon.Analysis.CountableOrdinalContinuous

/-! Full Corollary 4.10(ii), and Corollary 4.10(i) for every countable
ordinal. Finite coefficients are treated by actual finite reindexing;
infinite countable coefficients use the proved quantitative ordinal tower
theorem. The unrestricted uncountable-coefficient clause (i) is not claimed. -/
noncomputable section
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u) (α : Ordinal.{v})

theorem corollary_4_10_i_of_countable (hα : α < (Cardinal.aleph 1).ord) :
    Corollary_4_10_i 𝕜 Γ α := by
  by_cases hfinite : α < Ordinal.omega0
  · exact corollary_4_10_i_of_finite 𝕜 Γ α hfinite
  have hcoeff := ordinalContinuous_hasUPFP_of_countable_infinite 𝕜 hα (le_of_not_gt hfinite)
  letI := ordinalContinuous_separable 𝕜 hα
  intro hΓ p hp
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  have hsum : HasUPFP 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p.val) := by
    by_cases hp1 : p.val = 1
    · have hpEq : p = (⟨1, le_rfl⟩ : BanachExponent) := Subtype.ext hp1
      subst p
      exact (isWeaklyCompactlyGenerated_of_separable 𝕜
        (OrdinalContinuous 𝕜 α)).ellOne_hasUPFP hΓ hcoeff
    · exact lp_hasUPFP_of_uncountable_separable
        ((Cardinal.aleph0_le_aleph 1).trans_lt hΓ) p.val
        (lt_of_le_of_ne (Fact.out : 1 ≤ p.val) (Ne.symm hp1)) hp hcoeff
  refine ⟨hsum, ?_⟩
  have hp0 : 0 < p.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p.val))) hp
  exact hsum.isPrimary_of_sequenceSelfSimilar (Or.inl ⟨p,
    ⟨(lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (Γ := Γ)
      (X := OrdinalContinuous 𝕜 α) p.val hp0).toContinuousLinearEquiv⟩⟩)

theorem corollary_4_10_ii [TopologicalSpace Γ] [DiscreteTopology Γ] :
    Corollary_4_10_ii 𝕜 Γ α := by
  intro hα hΓ
  by_cases hfinite : α < Ordinal.omega0
  · exact corollary_4_10_ii_of_finite 𝕜 Γ α hfinite hα hΓ
  have hcoeff := ordinalContinuous_hasUPFP_of_countable_infinite 𝕜 hα (le_of_not_gt hfinite)
  letI := ordinalContinuous_separable 𝕜 hα
  exact ⟨fun p hp1 hp => lp_hasUPFP_of_uncountable_separable hΓ p.val hp1 hp hcoeff,
    cZero_hasUPFP_of_uncountable_separable hΓ hcoeff⟩

end PFP
