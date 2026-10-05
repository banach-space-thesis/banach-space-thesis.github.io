import Posets.OrdinalIdealTransportCountablePowers
import JLMS.OrdinalSpaceMultipleSum

/-! The actual repeated-block model C(κ·ω) ≃ c₀(ℕ,C(κ)), with uniformly
bounded endpoint-zero coordinate identifications. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance repeatedModelFunctionGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance repeatedModelFunctionSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance repeatedModelEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance repeatedModelEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def ordinalCountableMultipleSumEquiv (κ : Ordinal.{0}) (hκ : Ordinal.omega0 ≤ κ)
    (habs : Ordinal.omega0 = κ ∨ Ordinal.omega0 + κ = κ) :
    OrdinalC 𝕜 (κ * Ordinal.omega0) ≃L[𝕜] CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 κ) := by
  have hκprod : Ordinal.omega0 ≤ κ * Ordinal.omega0 := hκ.trans
    (by simpa only [mul_one] using mul_le_mul_left' Ordinal.one_lt_omega0.le κ)
  let e := ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) κ hκ
  have he : ‖e.toContinuousLinearMap‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _
    (by norm_num) (norm_ordinalSpaceEndpointZeroBoundedEquiv_le κ hκ)
  have hei : ‖e.symm.toContinuousLinearMap‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _
    (by norm_num) (norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le κ hκ)
  exact (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) (κ * Ordinal.omega0) hκprod).trans
    ((ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) κ Ordinal.omega0 hκ le_rfl habs).trans
      ((CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : Set.Iio (Ordinal.omega0 : Ordinal.{0}) =>
        ordinalEndpointZero 𝕜 κ) ordinalNatIioOmegaEquiv).toContinuousLinearEquiv.trans
        (CZeroSum.congrRight (fun _ : ℕ => e.symm) (by norm_num) (by norm_num)
          (fun _ => hei) (fun _ => he))))

def initialOrdinalCountableSumEquiv {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c) :
    OrdinalC 𝕜 (c.ord * Ordinal.omega0) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : ℕ => OrdinalC 𝕜 c.ord) := by
  have hκ : Ordinal.omega0 < c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_lt_ord.mpr hu
  exact ordinalCountableMultipleSumEquiv c.ord hκ.le (Or.inr
    (Ordinal.principal_add_iff_add_left_eq_self.mp (Ordinal.principal_add_ord hu.le) _ hκ))

theorem jlmsScalarCZero_hasUPFP :
    ThesisCommon.HasUPFP 𝕜 (CZeroSum 𝕜 (fun _ : ℕ => 𝕜)) :=
  (ordinalOmega_hasUPFP (𝕜 := 𝕜)).of_equiv (ordinalSpaceOmegaCZeroEquiv (𝕜 := 𝕜))

end Posets
