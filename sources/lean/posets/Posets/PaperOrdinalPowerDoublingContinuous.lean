import Posets.PaperOrdinalPowerDoubling

/-! The same bounded finite-height change for full continuous-function
spaces, using the actual endpoint-zero equivalences with bound two. -/

noncomputable section
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance powerDoublingContinuousFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance powerDoublingContinuousFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance powerDoublingContinuousEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerDoublingContinuousEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance

def paperOrdinalContinuousPowerMultipleEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    JLMS.OrdinalC 𝕜 (c.ord ^ (((m + 1) * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.OrdinalC 𝕜 (c.ord ^ (n : Ordinal)) :=
  (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
    (JLMS.ordinalInitialPower_infinite c hc _
      (by exact_mod_cast Nat.mul_le_mul (by omega : 1 ≤ m + 1) (by omega : 1 ≤ n)))).trans
    ((paperOrdinalPowerMultipleEquiv c hc n hn m).trans
      (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
        (JLMS.ordinalInitialPower_infinite c hc _ (by exact_mod_cast (by omega : 1 ≤ n)))).symm)

theorem paperOrdinalContinuousPowerMultipleEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ‖(paperOrdinalContinuousPowerMultipleEquiv (𝕜 := 𝕜) c hc n hn m).toContinuousLinearMap‖ ≤
      4 * 512 ^ m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  unfold paperOrdinalContinuousPowerMultipleEquiv
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply]
  calc
    _ ≤ 2 * ‖paperOrdinalPowerMultipleEquiv c hc n hn m
        (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ _ x)‖ :=
      JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _ _
    _ ≤ 2 * (512 ^ m * ‖JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ _ x‖) :=
      mul_le_mul_of_nonneg_left
        ((Classical.choose_spec (paperOrdinalPowerMultiple_exists c hc n hn m)).1 _) (by norm_num)
    _ ≤ 2 * (512 ^ m * (2 * ‖x‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _ x)
        (by positivity)) (by norm_num)
    _ = (4 * 512 ^ m) * ‖x‖ := by ring

theorem paperOrdinalContinuousPowerMultipleEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) (m : ℕ) :
    ‖(paperOrdinalContinuousPowerMultipleEquiv (𝕜 := 𝕜) c hc n hn m).symm.toContinuousLinearMap‖ ≤
      4 * 512 ^ m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  unfold paperOrdinalContinuousPowerMultipleEquiv
  simp only [ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm]
  calc
    _ ≤ 2 * ‖(paperOrdinalPowerMultipleEquiv c hc n hn m).symm
        (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ _ x)‖ :=
      JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _ _
    _ ≤ 2 * (512 ^ m * ‖JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ _ x‖) :=
      mul_le_mul_of_nonneg_left
        ((Classical.choose_spec (paperOrdinalPowerMultiple_exists c hc n hn m)).2 _) (by norm_num)
    _ ≤ 2 * (512 ^ m * (2 * ‖x‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _ x)
        (by positivity)) (by norm_num)
    _ = (4 * 512 ^ m) * ‖x‖ := by ring

def paperOrdinalContinuousPowerDoublingEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (n : ℕ) (hn : 2 ≤ n) :
    JLMS.OrdinalC 𝕜 (c.ord ^ ((2 * n : ℕ) : Ordinal)) ≃L[𝕜]
      JLMS.OrdinalC 𝕜 (c.ord ^ (n : Ordinal)) :=
  paperOrdinalContinuousPowerMultipleEquiv c hc n hn 1

theorem paperOrdinalContinuousPowerDoublingEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    ‖(paperOrdinalContinuousPowerDoublingEquiv (𝕜 := 𝕜) c hc n hn).toContinuousLinearMap‖ ≤ 2048 := by
  simpa only [pow_one, show (4 : ℝ) * 512 = 2048 by norm_num] using
    paperOrdinalContinuousPowerMultipleEquiv_norm_le (𝕜 := 𝕜) c hc n hn 1

theorem paperOrdinalContinuousPowerDoublingEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    ‖(paperOrdinalContinuousPowerDoublingEquiv (𝕜 := 𝕜) c hc n hn).symm.toContinuousLinearMap‖ ≤ 2048 := by
  simpa only [pow_one, show (4 : ℝ) * 512 = 2048 by norm_num] using
    paperOrdinalContinuousPowerMultipleEquiv_symm_norm_le (𝕜 := 𝕜) c hc n hn 1

end Posets
