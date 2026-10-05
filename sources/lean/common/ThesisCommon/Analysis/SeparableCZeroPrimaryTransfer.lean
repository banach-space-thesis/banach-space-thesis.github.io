import ThesisCommon.Analysis.SeparableCZeroPrimaryCoordinates
import ThesisCommon.Analysis.CZeroPrimaryCoordinatesTransfer
import ThesisCommon.Analysis.CountableSumSeparable

/-! Primariness of arbitrary uncountable c₀ sums from their countable
models, through actual invariant blocks and coordinate isometries. -/
noncomputable section
open TopologicalSpace
open scoped Cardinal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem cZero_isUniformlyPrimary_of_countable_model
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hprimary : IsUniformlyPrimary 𝕜 (CZeroSum X)) :
    IsUniformlyPrimary 𝕜 C₀(Γ, X) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ.le
  letI : SeparableSpace C₀(ℕ, X) := cZero_separableSpace_of_countable (𝕜 := 𝕜)
  have hcoords : HasPrimaryCZeroCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := C₀(ℕ, X)) :=
    fun P hP => separable_cZero_primary_coordinates hΓ P hP
  exact (HasPrimaryCZeroCoordinates.isUniformlyPrimary hΓ.le hcoords hprimary).of_isometry
    (cZeroArbitraryAbsorbCountableIsometry (𝕜 := 𝕜) (X := X) (Γ := Γ))

theorem cZero_isPrimary_of_countable_model
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (hprimary : IsPrimary 𝕜 (CZeroSum X)) : IsPrimary 𝕜 C₀(Γ, X) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ.le
  letI : SeparableSpace C₀(ℕ, X) := cZero_separableSpace_of_countable (𝕜 := 𝕜)
  have hcoords : HasPrimaryCZeroCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := C₀(ℕ, X)) :=
    fun P hP => separable_cZero_primary_coordinates hΓ P hP
  exact (HasPrimaryCZeroCoordinates.isPrimary hΓ.le hcoords hcof hprimary).of_equiv
    (cZeroArbitraryAbsorbCountableIsometry (𝕜 := 𝕜) (X := X) (Γ := Γ)).toContinuousLinearEquiv

end ThesisCommon
