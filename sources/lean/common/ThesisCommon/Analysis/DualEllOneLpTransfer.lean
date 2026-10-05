import ThesisCommon.Analysis.DualEllOneLpSeparable
import ThesisCommon.Analysis.SeparableRangeFactorizationTransfer
import ThesisCommon.Analysis.ConcreteUncountableSchauderSums
import ThesisCommon.Analysis.PrimaryIsomorphism
import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.PelczynskiDecomposition

/-! The large-index finite-p transfer for coefficients with an actual
ell-one dual. All coefficient and scalar-range hypotheses are explicit;
no ordinal classification is assumed by this helper. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 Γ X I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lp_hasUPFP_of_large_index_separable_scalar_ranges
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) p,
      TopologicalSpace.IsSeparable (Set.range S)) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (lp (fun _ : Γ => X) p) := by
  let hs := scalarLpSchauderFamily_symmetric (𝕜 := 𝕜) (Γ := Γ) p hp
  have h := UncountableSchauderSum.hasUPFP_of_separable_scalar_ranges hs hsep hΓ hX
  exact h.of_equiv (lpUncountableSchauderSumEquiv (Y := X) p hp hs.1).toContinuousLinearEquiv

theorem lp_hasUPFP_of_large_index_dual_equiv_ellOne
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (lp (fun _ : Γ => X) p) :=
  lp_hasUPFP_of_large_index_separable_scalar_ranges p hp hΓ
    (isSeparable_lp_range_of_dual_equiv_ellOne d p hp) hX

theorem lp_isPrimary_of_large_index_dual_equiv_ellOne [CompleteSpace X]
    (d : (X →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : I => 𝕜) 1)
    (p : BanachExponent) (hp : p.val ≠ ∞)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    IsPrimary 𝕜 (lp (fun _ : Γ => X) p.val) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  have hp0 : 0 < p.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p.val))) hp
  exact (lp_hasUPFP_of_large_index_dual_equiv_ellOne d p.val hp hΓ hX).isPrimary_of_sequenceSelfSimilar
    (Or.inl ⟨p, ⟨(lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (Γ := Γ)
      (X := X) p.val hp0).toContinuousLinearEquiv⟩⟩)

end ThesisCommon
