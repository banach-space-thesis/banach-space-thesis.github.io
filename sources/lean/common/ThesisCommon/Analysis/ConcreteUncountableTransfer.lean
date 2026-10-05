import ThesisCommon.Analysis.ConcreteUncountableSchauderSums
import ThesisCommon.Analysis.UncountableSchauderTransfer
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Concrete UPFP preservation for arbitrary uncountable ℓp and c₀ sums of
separable coefficient spaces. The transfer uses the actual scalar unit
families and the proved coordinate-preserving isometries.
-/
noncomputable section
open TopologicalSpace
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem lp_hasUPFP_of_uncountable_separable
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr hΓ.le
  let hs := scalarLpSchauderFamily_symmetric (𝕜 := 𝕜) (Γ := Γ) p hp
  have hnot := scalarLpSchauderFamily_not_equivalentEllOne (𝕜 := 𝕜) (Γ := Γ) p hp hp1
  have h := UncountableSchauderSum.hasUPFP_of_separable hs hnot hΓ hX
  exact h.of_equiv (lpUncountableSchauderSumEquiv (Y := X) p hp hs.1).toContinuousLinearEquiv

theorem cZero_hasUPFP_of_uncountable_separable
    [TopologicalSpace Γ] [DiscreteTopology Γ]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 C₀(Γ, X) := by
  letI : Infinite Γ := Cardinal.infinite_iff.mpr hΓ.le
  let hs := scalarCZeroSchauderFamily_symmetric (𝕜 := 𝕜) (Γ := Γ)
  have hnot := scalarCZeroSchauderFamily_not_equivalentEllOne (𝕜 := 𝕜) (Γ := Γ)
  have h := UncountableSchauderSum.hasUPFP_of_separable hs hnot hΓ hX
  exact h.of_equiv (cZeroUncountableSchauderSumEquiv (Y := X) hs.1).toContinuousLinearEquiv

end ThesisCommon
