import ThesisCommon.Analysis.SeparableLpPrimaryCoordinates
import ThesisCommon.Analysis.LpPrimaryCoordinatesTransfer
import ThesisCommon.Analysis.CountableSumSeparable

/-! Primariness of the actual uncountable finite-p sums, 1<p<infinity,
transferred from their countable models with all structural premises proved. -/
noncomputable section
open TopologicalSpace
open scoped Cardinal ENNReal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem lp_isUniformlyPrimary_of_countable_model (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hfin : p ≠ ∞) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hprimary : IsUniformlyPrimary 𝕜 (lp (fun _ : ℕ => X) p)) :
    IsUniformlyPrimary 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ.le
  letI : SeparableSpace (lp (fun _ : ℕ => X) p) := lp_separableSpace_of_countable (𝕜 := 𝕜) p hfin
  have hcoords : HasPrimaryLpCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := lp (fun _ : ℕ => X) p) p :=
    fun P hP => separable_lp_primary_coordinates p hp hfin hΓ P hP
  exact (HasPrimaryLpCoordinates.isUniformlyPrimary p (zero_lt_one.trans hp) hfin hΓ.le
    hcoords hprimary).of_isometry (lpArbitraryAbsorbCountableIsometry p (zero_lt_one.trans hp))

theorem lp_isPrimary_of_countable_model (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hfin : p ≠ ∞) (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (hprimary : IsPrimary 𝕜 (lp (fun _ : ℕ => X) p)) :
    IsPrimary 𝕜 (lp (fun _ : Γ => X) p) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ.le
  letI : SeparableSpace (lp (fun _ : ℕ => X) p) := lp_separableSpace_of_countable (𝕜 := 𝕜) p hfin
  have hcoords : HasPrimaryLpCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := lp (fun _ : ℕ => X) p) p :=
    fun P hP => separable_lp_primary_coordinates p hp hfin hΓ P hP
  exact (HasPrimaryLpCoordinates.isPrimary p (zero_lt_one.trans hp) hfin hΓ.le
    hcoords hcof hprimary).of_equiv
      (lpArbitraryAbsorbCountableIsometry p (zero_lt_one.trans hp)).toContinuousLinearEquiv

end ThesisCommon
