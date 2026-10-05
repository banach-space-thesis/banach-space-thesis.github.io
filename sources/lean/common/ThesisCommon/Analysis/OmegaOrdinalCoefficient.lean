import ThesisCommon.Analysis.CountableCompactOnePoint
import ThesisCommon.Analysis.OnePointContinuousDecomposition
import ThesisCommon.Analysis.CountableOrdinalContinuous
import ThesisCommon.Analysis.ScalarSequencePrimary
import ThesisCommon.Analysis.ConcreteUncountableTransfer
import ThesisCommon.Analysis.WCGEllOneFactorizationTransfer
import ThesisCommon.Analysis.SeparableWeaklyCompactlyGenerated
import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.PelczynskiDecomposition

/-! The first infinite ordinal coefficient is an actual c₀ model. Its UPFP
and the two sum conclusions use this proved isomorphism, not an assumed
factorization theorem for arbitrary countable ordinals. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜]

def omegaOrdinalCZeroEquiv :
    OrdinalContinuous 𝕜 Ordinal.omega0.{u} ≃L[𝕜] CZeroSum 𝕜 :=
  (continuousMapHomeomorphEquiv countableCompactOmegaOnePointHomeomorph.{u}.symm).trans
    onePointContinuousCZeroEquiv

theorem omegaOrdinal_hasUPFP : HasUPFP 𝕜 (OrdinalContinuous 𝕜 Ordinal.omega0.{u}) :=
  scalar_cZero_hasUPFP.of_equiv (omegaOrdinalCZeroEquiv 𝕜).symm

theorem omegaOrdinal_separable :
    TopologicalSpace.SeparableSpace (OrdinalContinuous 𝕜 Ordinal.omega0.{u}) := by
  apply ordinalContinuous_separable
  simpa using Cardinal.ord_lt_ord.mpr Cardinal.aleph0_lt_aleph_one

variable {𝕜} {Γ : Type*}

theorem omegaOrdinal_lp_hasUPFP_of_large_index
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : HasUPFP 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 Ordinal.omega0.{u}) p) := by
  letI := omegaOrdinal_separable 𝕜
  by_cases hp1 : p = 1
  · subst p
    exact (isWeaklyCompactlyGenerated_of_separable 𝕜 _).ellOne_hasUPFP hΓ
      (omegaOrdinal_hasUPFP 𝕜)
  · exact lp_hasUPFP_of_uncountable_separable
      ((Cardinal.aleph0_le_aleph 1).trans_lt hΓ) p
      (lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)) hp (omegaOrdinal_hasUPFP 𝕜)

theorem omegaOrdinal_lp_primary_of_large_index
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : IsPrimary 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 Ordinal.omega0.{u}) p) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  exact (omegaOrdinal_lp_hasUPFP_of_large_index hΓ p hp).isPrimary_of_sequenceSelfSimilar
    (Or.inl ⟨⟨p, Fact.out⟩,
      ⟨(lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (Γ := Γ)
        (X := OrdinalContinuous 𝕜 Ordinal.omega0.{u}) p hp0).toContinuousLinearEquiv⟩⟩)

end ThesisCommon
