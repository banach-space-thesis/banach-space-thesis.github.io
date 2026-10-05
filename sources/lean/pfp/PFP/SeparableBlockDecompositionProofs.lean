import PFP.GeneralSumBlockStatements
import ThesisCommon.Analysis.LpInvariantBlocks
import ThesisCommon.Analysis.CZeroInvariantBlocks

/-! Both actual-space alternatives of Lemma 4.26, including the unrestricted
printed formula. Closing each block under both incoming and outgoing support
separates all blocks, so H is the full ordinal index set. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 Γ X : Type*) [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem lemma_4_26_asPrinted : Lemma_4_26_asPrinted 𝕜 Γ X := by
  intro hsep
  letI := hsep
  constructor
  · intro p hp hfin P hP
    have hpReal : 1 < p.val.toReal := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp
    obtain ⟨B, hB, hidem, hdiag⟩ := lp_invariant_countable_blocks p.val hpReal hfin P hP
    refine ⟨B, hB, hidem, Set.univ, ?_, fun α _ β _ hne => hdiag α β hne⟩
    simpa only [Cardinal.mk_univ] using Cardinal.mk_ord_toType (Cardinal.mk Γ)
  · intro P hP
    obtain ⟨B, hB, hidem, hdiag⟩ := cZero_invariant_countable_blocks P hP
    refine ⟨B, hB, hidem, Set.univ, ?_, fun α _ β _ hne => hdiag α β hne⟩
    simpa only [Cardinal.mk_univ] using Cardinal.mk_ord_toType (Cardinal.mk Γ)

theorem lemma_4_26_uncountable : Lemma_4_26 𝕜 Γ X := by
  intro _hΓ
  exact lemma_4_26_asPrinted 𝕜 Γ X

end PFP
