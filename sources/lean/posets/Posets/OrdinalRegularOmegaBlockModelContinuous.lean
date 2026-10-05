import Posets.OrdinalRegularOmegaBlockModel

/-! Full compact C-space blocks in the cofinal model of κ^ω. -/
noncomputable section
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance omegaFullBlockFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance omegaFullBlockFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance omegaFullBlockEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaFullBlockEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaFullBlockSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance omegaFullBlockSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalOmegaFullBlockCoordinate (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) (n : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)) ≃L[𝕜]
      JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal)) :=
  (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ (JLMS.ordinalInitialPower_infinite c hc _
    (by exact_mod_cast (one_le_two.trans (h0.trans (hh.monotone (Nat.zero_le n))))))).symm

def ordinalOmegaFullBlockCoordinates (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) :=
  JLMS.CZeroSum.congrRight (ordinalOmegaFullBlockCoordinate c hc h hh h0)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)
    (fun n => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _))
    (fun n => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _))

theorem ordinalOmegaFullBlockCoordinates_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)))) :
    ‖ordinalOmegaFullBlockCoordinates c hc h hh h0 x‖ ≤ 2 * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro n
  exact (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _ (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm n) (by norm_num))

theorem ordinalOmegaFullBlockCoordinates_symm_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal)))) :
    ‖(ordinalOmegaFullBlockCoordinates c hc h hh h0).symm x‖ ≤ 2 * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro n
  exact (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _ (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm n) (by norm_num))

def ordinalOmegaEndpointFullBlockSumEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (ordinalOmegaEndpointBlockSumEquiv c hc h hh h0).trans
    (ordinalOmegaFullBlockCoordinates c hc h hh h0)

theorem ordinalOmegaEndpointFullBlockSumEquiv_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0)) :
    ‖ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0 x‖ ≤ 16 * ‖x‖ := by
  have ha := ordinalOmegaFullBlockCoordinates_apply_norm_le c hc h hh h0
    (ordinalOmegaEndpointBlockSumEquiv c hc h hh h0 x)
  have hb := ordinalOmegaEndpointBlockSumEquiv_apply_norm_le c hc h hh h0 x
  exact ha.trans (by linarith)

theorem ordinalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal)))) :
    ‖(ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0).symm x‖ ≤ 16 * ‖x‖ := by
  have ha := ordinalOmegaEndpointBlockSumEquiv_symm_apply_norm_le c hc h hh h0
    ((ordinalOmegaFullBlockCoordinates c hc h hh h0).symm x)
  have hb := ordinalOmegaFullBlockCoordinates_symm_apply_norm_le c hc h hh h0 x
  exact ha.trans (by linarith)

theorem ordinalOmegaEndpointFullBlockSumEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaEndpointFullBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).toContinuousLinearMap‖ ≤ 16 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalOmegaEndpointFullBlockSumEquiv_apply_norm_le c hc h hh h0)

theorem ordinalOmegaEndpointFullBlockSumEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaEndpointFullBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).symm.toContinuousLinearMap‖ ≤ 16 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le c hc h hh h0)

def ordinalOmegaContinuousBlockSumEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    JLMS.OrdinalC 𝕜 (c.ord ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
    (JLMS.ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le)).trans
    (ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0)

theorem ordinalOmegaContinuousBlockSumEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaContinuousBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).toContinuousLinearMap‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ha := ordinalOmegaEndpointFullBlockSumEquiv_apply_norm_le c hc h hh h0
    (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
      (JLMS.ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le) x)
  have hb := JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _
    (JLMS.ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le) x
  exact ha.trans (by linarith)

theorem ordinalOmegaContinuousBlockSumEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaContinuousBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).symm.toContinuousLinearMap‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ha := JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _
    (JLMS.ordinalInitialPower_infinite c hc _ Ordinal.one_lt_omega0.le)
    ((ordinalOmegaEndpointFullBlockSumEquiv c hc h hh h0).symm x)
  have hb := ordinalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le c hc h hh h0 x
  exact ha.trans (by linarith)

end Posets
