import Posets.OrdinalRegularOmegaAssemblyEndpoint
import Posets.OrdinalRegularOmegaBlockModelContinuous

/-! Actual bounded models joining the half-open analytic ambient space to
the cofinal compact-block sum and the paper's original compact C-space. -/
noncomputable section
open Set
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
local instance ordinalOmegaModelsFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaModelsFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance ordinalOmegaModelsEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance ordinalOmegaModelsEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance ordinalOmegaModelsSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance ordinalOmegaModelsSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalHalfOpenContinuousEquiv (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    JLMS.CZero 𝕜 (Iio α) ≃L[𝕜] JLMS.OrdinalC 𝕜 α :=
  (ordinalEndpointCZeroIsometry (𝕜 := 𝕜) α).symm.toContinuousLinearEquiv.trans
    (JLMS.ordinalSpaceEndpointZeroBoundedEquiv α hα).symm

theorem ordinalHalfOpenContinuousEquiv_norm_le (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) :
    ‖(ordinalHalfOpenContinuousEquiv (𝕜 := 𝕜) α hα).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖(JLMS.ordinalSpaceEndpointZeroBoundedEquiv α hα).symm
    ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) α).symm f)‖ ≤ 2 * ‖f‖
  simpa only [LinearIsometryEquiv.norm_map] using
    JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le α hα
      ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) α).symm f)

theorem ordinalHalfOpenContinuousEquiv_symm_norm_le (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) :
    ‖(ordinalHalfOpenContinuousEquiv (𝕜 := 𝕜) α hα).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalEndpointCZeroIsometry (𝕜 := 𝕜) α (JLMS.ordinalSpaceEndpointZeroBoundedEquiv α hα f)‖ ≤ 2 * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le α hα f

def ordinalOmegaHalfOpenBlockSumEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm.toContinuousLinearEquiv.trans
    (ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0)

theorem ordinalOmegaHalfOpenBlockSumEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).toContinuousLinearMap‖ ≤ 16 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0
    ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm f)‖ ≤ 16 * ‖f‖
  simpa only [LinearIsometryEquiv.norm_map] using
    ordinalOmegaEndpointFullBlockSumEquiv_apply_norm_le c hc h hh h0
      ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm f)

theorem ordinalOmegaHalfOpenBlockSumEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).symm.toContinuousLinearMap‖ ≤ 16 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _
    ((ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0).symm f)‖ ≤ 16 * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact ordinalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le c hc h hh h0 f

end Posets

