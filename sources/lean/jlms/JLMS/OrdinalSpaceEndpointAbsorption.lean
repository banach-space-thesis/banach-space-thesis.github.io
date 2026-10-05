import JLMS.OrdinalSpaceEndpointZeroBounded
import JLMS.OrdinalSpaceSumAbsorption

/-!
# Uniform absorption for endpoint-zero ordinal function spaces

If γ+κ=κ and both ordinals are infinite, the endpoint-zero space at κ
absorbs the endpoint-zero space at γ. Both directions have norm at most
four. Together with c₀-sum absorption this removes the base summand in
Kislyakov Corollary 3.1.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance endpointAbsorptionFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointAbsorptionFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance

def ordinalSpaceAbsorptionIsometry (γ κ : Ordinal.{u}) (hκ : Ordinal.omega0 ≤ κ)
    (hγκ : γ + κ = κ) : OrdinalC 𝕜 γ × OrdinalC 𝕜 κ ≃ₗᵢ[𝕜] OrdinalC 𝕜 κ :=
  (ordinalSpaceAddIsometry γ κ hκ).symm.trans (ordinalSpaceCongrIsometry hγκ)

def ordinalEndpointZeroAbsorbLeft (γ κ : Ordinal.{u})
    (hγ : Ordinal.omega0 ≤ γ) (hκ : Ordinal.omega0 ≤ κ) (hγκ : γ + κ = κ) :
    (ordinalEndpointZero 𝕜 γ × ordinalEndpointZero 𝕜 κ) ≃L[𝕜] ordinalEndpointZero 𝕜 κ :=
  ((ordinalSpaceEndpointZeroBoundedEquiv γ hγ).symm.prodCongr
    (ordinalSpaceEndpointZeroBoundedEquiv κ hκ).symm).trans
      ((ordinalSpaceAbsorptionIsometry (𝕜 := 𝕜) γ κ hκ hγκ).toContinuousLinearEquiv.trans
        (ordinalSpaceEndpointZeroBoundedEquiv κ hκ))

theorem norm_ordinalEndpointZeroAbsorbLeft_le (γ κ : Ordinal.{u})
    (hγ : Ordinal.omega0 ≤ γ) (hκ : Ordinal.omega0 ≤ κ) (hγκ : γ + κ = κ)
    (f : ordinalEndpointZero 𝕜 γ × ordinalEndpointZero 𝕜 κ) :
    ‖ordinalEndpointZeroAbsorbLeft γ κ hγ hκ hγκ f‖ ≤ 4 * ‖f‖ := by
  let p : OrdinalC 𝕜 γ × OrdinalC 𝕜 κ :=
    ((ordinalSpaceEndpointZeroBoundedEquiv γ hγ).symm f.1,
      (ordinalSpaceEndpointZeroBoundedEquiv κ hκ).symm f.2)
  have hp : ‖p‖ ≤ 2 * ‖f‖ := by
    rw [Prod.norm_def]
    apply max_le
    · exact (norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le γ hγ f.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left ‖f.1‖ ‖f.2‖) (by norm_num))
    · exact (norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le κ hκ f.2).trans
        (mul_le_mul_of_nonneg_left (le_max_right ‖f.1‖ ‖f.2‖) (by norm_num))
  have hb := norm_ordinalSpaceEndpointZeroBoundedEquiv_le κ hκ
    (ordinalSpaceAbsorptionIsometry (𝕜 := 𝕜) γ κ hκ hγκ p)
  rw [LinearIsometryEquiv.norm_map] at hb
  change ‖ordinalEndpointZeroAbsorbLeft γ κ hγ hκ hγκ f‖ ≤ 2 * ‖p‖ at hb
  exact hb.trans (by linarith)

theorem norm_ordinalEndpointZeroAbsorbLeft_symm_le (γ κ : Ordinal.{u})
    (hγ : Ordinal.omega0 ≤ γ) (hκ : Ordinal.omega0 ≤ κ) (hγκ : γ + κ = κ)
    (f : ordinalEndpointZero 𝕜 κ) :
    ‖(ordinalEndpointZeroAbsorbLeft γ κ hγ hκ hγκ).symm f‖ ≤ 4 * ‖f‖ := by
  let p : OrdinalC 𝕜 γ × OrdinalC 𝕜 κ :=
    (ordinalSpaceAbsorptionIsometry (𝕜 := 𝕜) γ κ hκ hγκ).symm
      ((ordinalSpaceEndpointZeroBoundedEquiv κ hκ).symm f)
  have hp : ‖p‖ ≤ 2 * ‖f‖ := by
    rw [show ‖p‖ = ‖(ordinalSpaceEndpointZeroBoundedEquiv κ hκ).symm f‖ from
      (ordinalSpaceAbsorptionIsometry (𝕜 := 𝕜) γ κ hκ hγκ).symm.norm_map _]
    exact norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le κ hκ f
  change max ‖ordinalSpaceEndpointZeroBoundedEquiv γ hγ p.1‖
    ‖ordinalSpaceEndpointZeroBoundedEquiv κ hκ p.2‖ ≤ 4 * ‖f‖
  apply max_le
  · have h := norm_ordinalSpaceEndpointZeroBoundedEquiv_le γ hγ p.1
    have h₁ : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
    linarith
  · have h := norm_ordinalSpaceEndpointZeroBoundedEquiv_le κ hκ p.2
    have h₂ : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
    linarith

def ordinalEndpointZeroSumAbsorbLeft (I : Type*) [Infinite I] (γ κ : Ordinal.{u})
    (hγ : Ordinal.omega0 ≤ γ) (hκ : Ordinal.omega0 ≤ κ) (hγκ : γ + κ = κ) :
    (ordinalEndpointZero 𝕜 γ × CZeroSum 𝕜 (fun _ : I => ordinalEndpointZero 𝕜 κ)) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : I => ordinalEndpointZero 𝕜 κ) :=
  cZeroSumAbsorbs I (ordinalEndpointZeroAbsorbLeft γ κ hγ hκ hγκ)

end JLMS
