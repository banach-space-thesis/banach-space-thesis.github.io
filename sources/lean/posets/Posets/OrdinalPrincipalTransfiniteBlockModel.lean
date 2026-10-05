import Posets.OrdinalPrincipalTransfiniteSequence
import Posets.OrdinalSuccessorEndpointIsometry
import Posets.OrdinalRegularOmegaBlockModelNorms
import JLMS.OrdinalSpacePowerSuccessor

/-! A uniform model for any transfinite cofinal sequence of principal blocks.
Successor boundaries make each endpoint-zero block isometric to its actual
compact continuous-function space, even when the block rank is a limit. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance transfinitePrincipalFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance transfinitePrincipalFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.OrdinalC 𝕜 α) := inferInstance
local instance transfinitePrincipalEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance transfinitePrincipalEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance transfinitePrincipalSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance transfinitePrincipalSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

namespace OrdinalPrincipalTransfiniteSequence
variable {Λ Γ : Ordinal.{u}} (P : OrdinalPrincipalTransfiniteSequence Λ Γ)

def coordinatesIsometry :
    JLMS.CZeroSum 𝕜 (fun i : Iio Λ =>
      JLMS.ordinalEndpointZero 𝕜 (JLMS.ordinalSpaceBlockLength P.blockMap i)) ≃ₗᵢ[𝕜]
      JLMS.CZeroSum 𝕜 (fun i : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint i)) :=
  JLMS.CZeroSum.congrRightIsometry (fun i =>
    (JLMS.ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) (P.blockMap_length i)).trans
      (ordinalSuccessorEndpointIsometry (P.endpoint i)))
def endpointSplit : JLMS.ordinalEndpointZero 𝕜 Γ ≃L[𝕜]
    JLMS.ordinalEndpointZero 𝕜 Λ ×
      JLMS.CZeroSum 𝕜 (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) :=
  (JLMS.ordinalEndpointZeroBlocksEquiv P.blockMap P.blockMap_strictMono P.blockMap_zero
    P.blockMap_endpoint P.blockMap_infinite_blocks).trans
      ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr P.coordinatesIsometry.toContinuousLinearEquiv)

theorem endpointSplit_norm_le (f : JLMS.ordinalEndpointZero 𝕜 Γ) :
    ‖P.endpointSplit f‖ ≤ 2 * ‖f‖ := by
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) P.blockMap P.blockMap_strictMono
    P.blockMap_zero P.blockMap_endpoint P.blockMap_infinite_blocks
  change max ‖(e f).1‖ ‖P.coordinatesIsometry (e f).2‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact JLMS.norm_ordinalEndpointZeroBlocksEquiv_apply_le _ _ _ _ _ f

theorem endpointSplit_symm_norm_le
    (f : JLMS.ordinalEndpointZero 𝕜 Λ ×
      JLMS.CZeroSum 𝕜 (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n))) :
    ‖P.endpointSplit.symm f‖ ≤ 2 * ‖f‖ := by
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜) P.blockMap P.blockMap_strictMono
    P.blockMap_zero P.blockMap_endpoint P.blockMap_infinite_blocks
  change ‖e.symm (f.1, P.coordinatesIsometry.symm f.2)‖ ≤ _
  calc
    _ ≤ 2 * ‖(f.1, P.coordinatesIsometry.symm f.2)‖ :=
      JLMS.norm_ordinalEndpointZeroBlocksEquiv_symm_apply_le _ _ _ _ _ _
    _ = 2 * ‖f‖ := by simp only [Prod.norm_def, LinearIsometryEquiv.norm_map]

theorem head_absorption : Λ + succ (P.endpoint P.zeroIndex) = succ (P.endpoint P.zeroIndex) := by
  rw [Ordinal.add_succ]
  exact congrArg succ (Ordinal.principal_add_iff_add_left_eq_self.mp (P.principal P.zeroIndex) _ P.head_large)

def headAbsorption :
    (JLMS.ordinalEndpointZero 𝕜 Λ × JLMS.OrdinalC 𝕜 (P.endpoint P.zeroIndex)) ≃L[𝕜]
      JLMS.OrdinalC 𝕜 (P.endpoint P.zeroIndex) :=
  ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
    (ordinalSuccessorEndpointIsometry (𝕜 := 𝕜) (P.endpoint P.zeroIndex)).symm.toContinuousLinearEquiv).trans
      ((JLMS.ordinalEndpointZeroAbsorbLeft _ _ P.infinite ((P.infinite.trans P.head_large.le).trans (Order.le_succ _))
        P.head_absorption).trans
          (ordinalSuccessorEndpointIsometry (P.endpoint P.zeroIndex)).toContinuousLinearEquiv)

theorem headAbsorption_norm_le
    (f : JLMS.ordinalEndpointZero 𝕜 Λ × JLMS.OrdinalC 𝕜 (P.endpoint P.zeroIndex)) :
    ‖P.headAbsorption f‖ ≤ 4 * ‖f‖ := by
  change ‖ordinalSuccessorEndpointIsometry (𝕜 := 𝕜) (P.endpoint P.zeroIndex)
    (JLMS.ordinalEndpointZeroAbsorbLeft _ _ P.infinite _ P.head_absorption
      (f.1, (ordinalSuccessorEndpointIsometry (𝕜 := 𝕜) (P.endpoint P.zeroIndex)).symm f.2))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [Prod.norm_def, LinearIsometryEquiv.norm_map] using
    JLMS.norm_ordinalEndpointZeroAbsorbLeft_le _ _ P.infinite _ P.head_absorption
      (f.1, (ordinalSuccessorEndpointIsometry (𝕜 := 𝕜) (P.endpoint P.zeroIndex)).symm f.2)

theorem headAbsorption_symm_norm_le (f : JLMS.OrdinalC 𝕜 (P.endpoint P.zeroIndex)) :
    ‖P.headAbsorption.symm f‖ ≤ 4 * ‖f‖ := by
  let d := ordinalSuccessorEndpointIsometry (𝕜 := 𝕜) (P.endpoint P.zeroIndex)
  let e := JLMS.ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) Λ
    (succ (P.endpoint P.zeroIndex)) P.infinite
    ((P.infinite.trans P.head_large.le).trans (Order.le_succ _)) P.head_absorption
  change ‖((e.symm (d.symm f)).1, d (e.symm (d.symm f)).2)‖ ≤ _
  calc
    _ = ‖e.symm (d.symm f)‖ := by simp only [Prod.norm_def, d.norm_map]
    _ ≤ 4 * ‖d.symm f‖ := JLMS.norm_ordinalEndpointZeroAbsorbLeft_symm_le
      (𝕜 := 𝕜) Λ (succ (P.endpoint P.zeroIndex)) P.infinite
      ((P.infinite.trans P.head_large.le).trans (Order.le_succ _)) P.head_absorption _
    _ = 4 * ‖f‖ := by rw [d.symm.norm_map]

def endpointBlockSumEquiv : JLMS.ordinalEndpointZero 𝕜 Γ ≃L[𝕜]
    JLMS.CZeroSum 𝕜 (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) :=
  P.endpointSplit.trans (JLMS.cZeroSumAbsorbsAt
    (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) P.zeroIndex P.headAbsorption)

theorem endpointBlockSumEquiv_norm_le (f : JLMS.ordinalEndpointZero 𝕜 Γ) :
    ‖P.endpointBlockSumEquiv f‖ ≤ 8 * ‖f‖ := by
  have h := ordinalOmegaBlock_absorbsAt_norm_le
    (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) P.zeroIndex P.headAbsorption
    (C := 4) (by norm_num) P.headAbsorption_norm_le (P.endpointSplit f)
  exact h.trans (by have hs := P.endpointSplit_norm_le f; linarith)

theorem endpointBlockSumEquiv_symm_norm_le
    (f : JLMS.CZeroSum 𝕜 (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n))) :
    ‖P.endpointBlockSumEquiv.symm f‖ ≤ 8 * ‖f‖ := by
  let a := JLMS.cZeroSumAbsorbsAt (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) P.zeroIndex P.headAbsorption
  have h := ordinalOmegaBlock_absorbsAt_symm_norm_le
    (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) P.zeroIndex P.headAbsorption
    (C := 4) (by norm_num) P.headAbsorption_symm_norm_le f
  have hs := P.endpointSplit_symm_norm_le (a.symm f)
  exact hs.trans (by linarith)

def halfOpenBlockSumEquiv : JLMS.CZero 𝕜 (Iio Γ) ≃L[𝕜]
    JLMS.CZeroSum 𝕜 (fun n : Iio Λ => JLMS.OrdinalC 𝕜 (P.endpoint n)) :=
  (ordinalEndpointCZeroIsometry (𝕜 := 𝕜) Γ).symm.toContinuousLinearEquiv.trans P.endpointBlockSumEquiv

theorem halfOpenBlockSumEquiv_norm_le :
    ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).toContinuousLinearMap‖ ≤ 8 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [halfOpenBlockSumEquiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.norm_map] using
    P.endpointBlockSumEquiv_norm_le ((ordinalEndpointCZeroIsometry (𝕜 := 𝕜) Γ).symm f)

theorem halfOpenBlockSumEquiv_symm_norm_le :
    ‖(P.halfOpenBlockSumEquiv (𝕜 := 𝕜)).symm.toContinuousLinearMap‖ ≤ 8 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖ordinalEndpointCZeroIsometry (𝕜 := 𝕜) Γ (P.endpointBlockSumEquiv.symm f)‖ ≤ 8 * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact P.endpointBlockSumEquiv_symm_norm_le f

end OrdinalPrincipalTransfiniteSequence
end Posets
