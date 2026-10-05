import ThesisCommon.Analysis.DualEllOneLpTransfer
import ThesisCommon.Analysis.DualDirectSums
import JLMS.Rudin
import JLMS.CompactCZeroEquiv
import PFP.MainStatements

/-! The scalar-range hypothesis in Corollary 4.10(i) for every ordinal,
with no countability or cofinality restriction. Rudin's actual atomic dual
isomorphism and Schur's theorem give a direct countable-support proof. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 Γ K : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]

def scatteredContinuousDualEllOneEquiv (hK : JLMS.IsScattered K) :
    (C(K, 𝕜) →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : K => 𝕜) 1 :=
  (banachDualEquiv (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K)).toContinuousLinearEquiv).trans
    (JLMS.exists_atomicDualModel (𝕜 := 𝕜) hK).some.representation.toContinuousLinearEquiv

theorem scatteredContinuous_lp_operator_separable_range (hK : JLMS.IsScattered K)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : C(K, 𝕜) →L[𝕜] lp (fun _ : Γ => 𝕜) p) :
    TopologicalSpace.IsSeparable (Set.range T) :=
  isSeparable_lp_range_of_dual_equiv_ellOne (scatteredContinuousDualEllOneEquiv hK) p hp T

def ordinalContinuousDualEllOneEquiv (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal) :
    (OrdinalContinuous 𝕜 α →L[𝕜] 𝕜) ≃L[𝕜] lp (fun _ : OrdinalInterval α => 𝕜) 1 :=
  scatteredContinuousDualEllOneEquiv (JLMS.scattered_ordinalInterval α)

theorem ordinalContinuous_lp_operator_separable_range (𝕜 : Type*) [RCLike 𝕜]
    (α : Ordinal) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : OrdinalContinuous 𝕜 α →L[𝕜] lp (fun _ : Γ => 𝕜) p) :
    TopologicalSpace.IsSeparable (Set.range T) :=
  isSeparable_lp_range_of_dual_equiv_ellOne (ordinalContinuousDualEllOneEquiv 𝕜 α) p hp T

/-- The reduction is conditional only on the displayed coefficient UPFP;
the separable-range requirement is proved for every ordinal above. -/
theorem corollary_4_10_i_of_coefficient_hasUPFP (𝕜 : Type*) [RCLike 𝕜]
    (Γ : Type*) (α : Ordinal) (hα : HasUPFP 𝕜 (OrdinalContinuous 𝕜 α)) :
    Corollary_4_10_i 𝕜 Γ α := by
  intro hΓ p hp
  let d := ordinalContinuousDualEllOneEquiv 𝕜 α
  exact ⟨lp_hasUPFP_of_large_index_dual_equiv_ellOne d p.val hp hΓ hα,
    lp_isPrimary_of_large_index_dual_equiv_ellOne d p hp hΓ hα⟩

end PFP
