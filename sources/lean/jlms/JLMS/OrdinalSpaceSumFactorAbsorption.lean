import JLMS.OrdinalSpaceMultipleSum

/-!
# Absorbing many copies of a smaller ordinal space

Combining the constant-block decomposition with absorption of an ordinal
prefix gives the adjacent-coordinate absorption used in Kislyakov's
singular-cardinal argument. The bounds are uniform in all three ordinals.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance sumFactorFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance sumFactorFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance sumFactorEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance sumFactorEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def ordinalEndpointZeroSumFactorAbsorption (δ η ε : Ordinal.{u})
    (hδ : Ordinal.omega0 ≤ δ) (hη : Ordinal.omega0 ≤ η) (hε : Ordinal.omega0 ≤ ε)
    (habs : η = δ ∨ η + δ = δ) (hfactor : δ * η + ε = ε) :
    ordinalEndpointZero 𝕜 ε ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio η => ordinalEndpointZero 𝕜 δ) × ordinalEndpointZero 𝕜 ε :=
  have hδη : Ordinal.omega0 ≤ δ * η :=
    hδ.trans (Ordinal.le_mul_left δ (Ordinal.omega0_pos.trans_le hη))
  (ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) (δ * η) ε hδη hε hfactor).symm.trans
    ((ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) δ η hδ hη habs).prodCongr
      (ContinuousLinearEquiv.refl 𝕜 _))

theorem norm_ordinalEndpointZeroSumFactorAbsorption_le (δ η ε : Ordinal.{u})
    (hδ : Ordinal.omega0 ≤ δ) (hη : Ordinal.omega0 ≤ η) (hε : Ordinal.omega0 ≤ ε)
    (habs : η = δ ∨ η + δ = δ) (hfactor : δ * η + ε = ε)
    (f : ordinalEndpointZero 𝕜 ε) :
    ‖ordinalEndpointZeroSumFactorAbsorption (𝕜 := 𝕜) δ η ε hδ hη hε habs hfactor f‖ ≤ 32 * ‖f‖ := by
  have hδη : Ordinal.omega0 ≤ δ * η :=
    hδ.trans (Ordinal.le_mul_left δ (Ordinal.omega0_pos.trans_le hη))
  let p := (ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) (δ * η) ε hδη hε hfactor).symm f
  have hp : ‖p‖ ≤ 4 * ‖f‖ := norm_ordinalEndpointZeroAbsorbLeft_symm_le _ _ _ _ _ f
  change max ‖ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) δ η hδ hη habs p.1‖ ‖p.2‖ ≤ _
  have hp₁ : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
  have hp₂ : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
  have hb := norm_ordinalEndpointZeroMultipleSumEquiv_le δ η hδ hη habs p.1
  apply max_le <;> nlinarith [norm_nonneg f]

theorem norm_ordinalEndpointZeroSumFactorAbsorption_symm_le (δ η ε : Ordinal.{u})
    (hδ : Ordinal.omega0 ≤ δ) (hη : Ordinal.omega0 ≤ η) (hε : Ordinal.omega0 ≤ ε)
    (habs : η = δ ∨ η + δ = δ) (hfactor : δ * η + ε = ε)
    (f : CZeroSum 𝕜 (fun _ : Set.Iio η => ordinalEndpointZero 𝕜 δ) × ordinalEndpointZero 𝕜 ε) :
    ‖(ordinalEndpointZeroSumFactorAbsorption (𝕜 := 𝕜) δ η ε hδ hη hε habs hfactor).symm f‖
      ≤ 32 * ‖f‖ := by
  have hδη : Ordinal.omega0 ≤ δ * η :=
    hδ.trans (Ordinal.le_mul_left δ (Ordinal.omega0_pos.trans_le hη))
  let p : ordinalEndpointZero 𝕜 (δ * η) × ordinalEndpointZero 𝕜 ε :=
    ((ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) δ η hδ hη habs).symm f.1, f.2)
  have hp : ‖p‖ ≤ 8 * ‖f‖ := by
    change max ‖(ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) δ η hδ hη habs).symm f.1‖ ‖f.2‖ ≤ _
    apply max_le
    · exact (norm_ordinalEndpointZeroMultipleSumEquiv_symm_le δ η hδ hη habs f.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · exact (le_max_right _ _).trans (le_mul_of_one_le_left (norm_nonneg f) (by norm_num))
  have hb := norm_ordinalEndpointZeroAbsorbLeft_le (δ * η) ε hδη hε hfactor p
  change ‖(ordinalEndpointZeroSumFactorAbsorption (𝕜 := 𝕜) δ η ε hδ hη hε habs hfactor).symm f‖
    ≤ 4 * ‖p‖ at hb
  linarith

end JLMS
