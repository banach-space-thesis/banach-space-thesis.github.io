import Posets.OrdinalPrincipalOmegaBlockModel
import Posets.OrdinalRegularOmegaAssemblyEndpoint

/-! Full compact C-space blocks in the cofinal model of B^ω for an additively principal base larger than ω. -/
noncomputable section
open Set
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance principalOmegaFullBlockFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance principalOmegaFullBlockFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance principalOmegaFullBlockEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance principalOmegaFullBlockEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance principalOmegaFullBlockSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance principalOmegaFullBlockSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalPrincipalOmegaFullBlockCoordinate (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) (n : ℕ) :
    JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)) ≃L[𝕜]
      JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal)) :=
  (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _ (ordinalPrincipalFinitePower_infinite B hB.le _
    (by exact_mod_cast h0.trans (hh.monotone (Nat.zero_le n))))).symm

def ordinalPrincipalOmegaFullBlockCoordinates (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) :=
  JLMS.CZeroSum.congrRight (ordinalPrincipalOmegaFullBlockCoordinate B hB hP h hh h0)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)
    (fun n => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _))
    (fun n => ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _))

theorem ordinalPrincipalOmegaFullBlockCoordinates_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)))) :
    ‖ordinalPrincipalOmegaFullBlockCoordinates B hB hP h hh h0 x‖ ≤ 2 * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro n
  exact (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _ (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm n) (by norm_num))

theorem ordinalPrincipalOmegaFullBlockCoordinates_symm_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal)))) :
    ‖(ordinalPrincipalOmegaFullBlockCoordinates B hB hP h hh h0).symm x‖ ≤ 2 * ‖x‖ := by
  apply JLMS.CZeroSum.norm_le (by positivity)
  intro n
  exact (JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _ (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_apply_le_norm n) (by norm_num))

def ordinalPrincipalOmegaEndpointFullBlockSumEquiv (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) :=
  (ordinalPrincipalOmegaEndpointBlockSumEquiv B hB hP h hh h0).trans
    (ordinalPrincipalOmegaFullBlockCoordinates B hB hP h hh h0)

theorem ordinalPrincipalOmegaEndpointFullBlockSumEquiv_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0)) :
    ‖ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0 x‖ ≤ 16 * ‖x‖ := by
  have ha := ordinalPrincipalOmegaFullBlockCoordinates_apply_norm_le B hB hP h hh h0
    (ordinalPrincipalOmegaEndpointBlockSumEquiv B hB hP h hh h0 x)
  have hb := ordinalPrincipalOmegaEndpointBlockSumEquiv_apply_norm_le B hB hP h hh h0 x
  exact ha.trans (by linarith)

theorem ordinalPrincipalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal)))) :
    ‖(ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0).symm x‖ ≤ 16 * ‖x‖ := by
  have ha := ordinalPrincipalOmegaEndpointBlockSumEquiv_symm_apply_norm_le B hB hP h hh h0
    ((ordinalPrincipalOmegaFullBlockCoordinates B hB hP h hh h0).symm x)
  have hb := ordinalPrincipalOmegaFullBlockCoordinates_symm_apply_norm_le B hB hP h hh h0 x
  exact ha.trans (by linarith)

theorem ordinalPrincipalOmegaEndpointFullBlockSumEquiv_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaEndpointFullBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).toContinuousLinearMap‖ ≤ 16 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalPrincipalOmegaEndpointFullBlockSumEquiv_apply_norm_le B hB hP h hh h0)

theorem ordinalPrincipalOmegaEndpointFullBlockSumEquiv_symm_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaEndpointFullBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).symm.toContinuousLinearMap‖ ≤ 16 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalPrincipalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le B hB hP h hh h0)

def ordinalPrincipalOmegaContinuousBlockSumEquiv (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.OrdinalC 𝕜 (B ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) :=
  (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
    (ordinalPrincipalFinitePower_infinite B hB.le _ Ordinal.one_lt_omega0.le)).trans
    (ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0)

theorem ordinalPrincipalOmegaContinuousBlockSumEquiv_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaContinuousBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).toContinuousLinearMap‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ha := ordinalPrincipalOmegaEndpointFullBlockSumEquiv_apply_norm_le B hB hP h hh h0
    (JLMS.ordinalSpaceEndpointZeroBoundedEquiv _
      (ordinalPrincipalFinitePower_infinite B hB.le _ Ordinal.one_lt_omega0.le) x)
  have hb := JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_le _
    (ordinalPrincipalFinitePower_infinite B hB.le _ Ordinal.one_lt_omega0.le) x
  exact ha.trans (by linarith)

theorem ordinalPrincipalOmegaContinuousBlockSumEquiv_symm_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaContinuousBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).symm.toContinuousLinearMap‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ha := JLMS.norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _
    (ordinalPrincipalFinitePower_infinite B hB.le _ Ordinal.one_lt_omega0.le)
    ((ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0).symm x)
  have hb := ordinalPrincipalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le B hB hP h hh h0 x
  exact ha.trans (by linarith)

def ordinalPrincipalOmegaHalfOpenBlockSumEquiv (B : Ordinal.{u})
    (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.CZero 𝕜 (Iio (B ^ Ordinal.omega0)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.OrdinalC 𝕜 (B ^ (h n : Ordinal))) :=
  (ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm.toContinuousLinearEquiv.trans
    (ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0)

theorem ordinalPrincipalOmegaHalfOpenBlockSumEquiv_norm_le (B : Ordinal.{u})
    (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).toContinuousLinearMap‖ ≤ 16 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0
    ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm f)‖ ≤ 16 * ‖f‖
  simpa only [LinearIsometryEquiv.norm_map] using
    ordinalPrincipalOmegaEndpointFullBlockSumEquiv_apply_norm_le B hB hP h hh h0
      ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _).symm f)

theorem ordinalPrincipalOmegaHalfOpenBlockSumEquiv_symm_norm_le (B : Ordinal.{u})
    (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaHalfOpenBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).symm.toContinuousLinearMap‖ ≤ 16 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalEndpointCZeroIsometry (𝕜 := 𝕜) _
    ((ordinalPrincipalOmegaEndpointFullBlockSumEquiv B hB hP h hh h0).symm f)‖ ≤ 16 * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact ordinalPrincipalOmegaEndpointFullBlockSumEquiv_symm_apply_norm_le B hB hP h hh h0 f

end Posets

