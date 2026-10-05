import ThesisCommon.Analysis.FiniteCoefficientAbsorption
import ThesisCommon.Analysis.ConcreteUncountableTransfer
import ThesisCommon.Analysis.WCGEllOneFactorizationTransfer
import ThesisCommon.Analysis.SeparableWeaklyCompactlyGenerated
import ThesisCommon.Analysis.ScalarPrimary
import ThesisCommon.Analysis.PelczynskiDecomposition

/-! Genuine UPFP and primariness consequences for nonzero finite-dimensional
coefficients. These avoid the invalid assumption that every such coefficient
space itself has PFP. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [FiniteDimensional 𝕜 X] [Nontrivial X]

theorem finiteCoefficient_lp_hasUPFP
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) : HasUPFP 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr hΓ.le
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have h := lp_hasUPFP_of_uncountable_separable (𝕜 := 𝕜) (X := 𝕜)
    hΓ p hp1 hp scalar_hasUPFP
  exact h.of_equiv (lpFiniteCoefficientEquiv (𝕜 := 𝕜) (Γ := Γ) (X := X) p hp0).symm

theorem finiteCoefficient_cZero_hasUPFP [TopologicalSpace Γ] [DiscreteTopology Γ]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) : HasUPFP 𝕜 C₀(Γ, X) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr hΓ.le
  have h := cZero_hasUPFP_of_uncountable_separable (𝕜 := 𝕜) (X := 𝕜) hΓ scalar_hasUPFP
  exact h.of_equiv (cZeroFiniteCoefficientEquiv (𝕜 := 𝕜) (Γ := Γ) (X := X)).symm

theorem finiteCoefficient_lp_hasUPFP_of_large_index
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : HasUPFP 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  by_cases hp1 : p = 1
  · subst p
    have h := (isWeaklyCompactlyGenerated_of_separable 𝕜 𝕜).ellOne_hasUPFP hΓ scalar_hasUPFP
    exact h.of_equiv (lpFiniteCoefficientEquiv (𝕜 := 𝕜) (Γ := Γ) (X := X) 1
      (by norm_num)).symm
  · exact finiteCoefficient_lp_hasUPFP ((Cardinal.aleph0_le_aleph 1).trans_lt hΓ) p
      (lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)) hp

theorem finiteCoefficient_lp_primary_of_large_index
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : IsPrimary 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  have h := finiteCoefficient_lp_hasUPFP_of_large_index (𝕜 := 𝕜) (X := X) hΓ p hp
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  exact h.isPrimary_of_sequenceSelfSimilar (Or.inl ⟨⟨p, Fact.out⟩,
    ⟨(lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (Γ := Γ) (X := X) p hp0).toContinuousLinearEquiv⟩⟩)

end ThesisCommon
