import Posets.OrdinalPrincipalOmegaBlockGeometry
import Posets.OrdinalRegularOmegaBlockModelNorms
import JLMS.OrdinalSpacePowerSuccessor

/-! The endpoint-zero space at B^ω for any infinite additively principal base is uniformly equivalent to the
c₀ sum along any strictly increasing positive finite heights. -/

noncomputable section
open Set Order
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance principalOmegaBlockModelEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance principalOmegaBlockModelEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance principalOmegaBlockModelSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance principalOmegaBlockModelSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalPrincipalOmegaBlockCoordinatesIsometry (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.CZeroSum 𝕜 (fun ξ : Iio (Ordinal.omega0 : Ordinal.{u}) =>
      JLMS.ordinalEndpointZero 𝕜 (JLMS.ordinalSpaceBlockLength
        (ordinalOmegaBlockMap B
          (Ordinal.one_lt_omega0.trans_le hB.le) h hh h0) ξ)) ≃ₗᵢ[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) :=
  (JLMS.CZeroSum.reindex (𝕜 := 𝕜) ordinalOmegaNatIndexEquiv).trans
    (JLMS.CZeroSum.congrRightIsometry (fun n => JLMS.ordinalEndpointZeroCongrIsometry
      (ordinalPrincipalOmegaBlockMap_length B hB.le hP h hh h0 n)))

def ordinalPrincipalOmegaEndpointSplit (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
        JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) :=
  (JLMS.ordinalEndpointZeroBlocksEquiv
    (ordinalOmegaBlockMap B
      (Ordinal.one_lt_omega0.trans_le hB.le) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0)
    (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0)
    (ordinalPrincipalOmegaBlockMap_infinite_blocks B hB.le hP h hh h0)).trans
    ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
      (ordinalPrincipalOmegaBlockCoordinatesIsometry B hB hP h hh h0).toContinuousLinearEquiv)

theorem ordinalPrincipalOmegaEndpointSplit_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0)) :
    ‖ordinalPrincipalOmegaEndpointSplit B hB hP h hh h0 x‖ ≤ 2 * ‖x‖ := by
  let d := ordinalPrincipalOmegaBlockCoordinatesIsometry (𝕜 := 𝕜) B hB hP h hh h0
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalOmegaBlockMap B
      (Ordinal.one_lt_omega0.trans_le hB.le) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0) (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0) (ordinalPrincipalOmegaBlockMap_infinite_blocks B hB.le hP h hh h0)
  change max ‖(e x).1‖ ‖d (e x).2‖ ≤ _
  rw [d.norm_map]
  exact JLMS.norm_ordinalEndpointZeroBlocksEquiv_apply_le _ _ _ _ _ x

theorem ordinalPrincipalOmegaEndpointSplit_symm_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)))) :
    ‖(ordinalPrincipalOmegaEndpointSplit B hB hP h hh h0).symm x‖ ≤ 2 * ‖x‖ := by
  let d := ordinalPrincipalOmegaBlockCoordinatesIsometry (𝕜 := 𝕜) B hB hP h hh h0
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalOmegaBlockMap B
      (Ordinal.one_lt_omega0.trans_le hB.le) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0) (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0) (ordinalPrincipalOmegaBlockMap_infinite_blocks B hB.le hP h hh h0)
  change ‖e.symm (x.1, d.symm x.2)‖ ≤ _
  calc
    _ ≤ 2 * ‖(x.1, d.symm x.2)‖ := JLMS.norm_ordinalEndpointZeroBlocksEquiv_symm_apply_le _ _ _ _ _ _
    _ = 2 * ‖x‖ := by simp only [Prod.norm_def, d.symm.norm_map]

def ordinalPrincipalOmegaBlockHeadAbsorption (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (h0 : 1 ≤ h 0) :
    (JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
      JLMS.ordinalEndpointZero 𝕜 (B ^ (h 0 : Ordinal))) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (B ^ (h 0 : Ordinal)) :=
  JLMS.ordinalEndpointZeroAbsorbLeft _ _ le_rfl
    (ordinalPrincipalFinitePower_infinite B hB.le _ (by exact_mod_cast (by omega : 1 ≤ h 0)))
    (ordinalPrincipalOmegaBlock_head_absorption B hB hP h h0)

def ordinalPrincipalOmegaEndpointBlockSumEquiv (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) :=
  (ordinalPrincipalOmegaEndpointSplit B hB hP h hh (by omega)).trans
    (JLMS.cZeroSumAbsorbsAt (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)))
      0 (ordinalPrincipalOmegaBlockHeadAbsorption B hB hP h h0))

theorem ordinalPrincipalOmegaBlockHeadAbsorption_symm_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (B ^ (h 0 : Ordinal))) :
    ‖(ordinalPrincipalOmegaBlockHeadAbsorption B hB hP h h0).symm x‖ ≤ 4 * ‖x‖ :=
  JLMS.norm_ordinalEndpointZeroAbsorbLeft_symm_le Ordinal.omega0
    (B ^ (h 0 : Ordinal)) le_rfl
    (ordinalPrincipalFinitePower_infinite B hB.le _ (by exact_mod_cast (by omega : 1 ≤ h 0)))
    (ordinalPrincipalOmegaBlock_head_absorption B hB hP h h0) x

theorem ordinalPrincipalOmegaEndpointBlockSumEquiv_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (B ^ Ordinal.omega0)) :
    ‖ordinalPrincipalOmegaEndpointBlockSumEquiv B hB hP h hh h0 x‖ ≤ 8 * ‖x‖ := by
  have hn := ordinalOmegaBlock_absorbsAt_norm_le
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) 0
    (ordinalPrincipalOmegaBlockHeadAbsorption B hB hP h h0) (C := 4) (by norm_num)
    (JLMS.norm_ordinalEndpointZeroAbsorbLeft_le _ _ _ _ _)
    (ordinalPrincipalOmegaEndpointSplit B hB hP h hh (by omega) x)
  have hs := ordinalPrincipalOmegaEndpointSplit_norm_le B hB hP h hh (by omega) x
  exact hn.trans (by linarith)

theorem ordinalPrincipalOmegaEndpointBlockSumEquiv_symm_apply_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)))) :
    ‖(ordinalPrincipalOmegaEndpointBlockSumEquiv B hB hP h hh h0).symm x‖ ≤ 8 * ‖x‖ := by
  let a := JLMS.cZeroSumAbsorbsAt
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal)))
    0 (ordinalPrincipalOmegaBlockHeadAbsorption B hB hP h h0)
  have hn := ordinalOmegaBlock_absorbsAt_symm_norm_le
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (B ^ (h n : Ordinal))) 0
    (ordinalPrincipalOmegaBlockHeadAbsorption B hB hP h h0) (C := 4) (by norm_num)
    (ordinalPrincipalOmegaBlockHeadAbsorption_symm_norm_le B hB hP h h0) x
  have hs := ordinalPrincipalOmegaEndpointSplit_symm_norm_le B hB hP h hh (by omega) (a.symm x)
  exact hs.trans (by linarith)

theorem ordinalPrincipalOmegaEndpointBlockSumEquiv_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaEndpointBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).toContinuousLinearMap‖ ≤ 8 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalPrincipalOmegaEndpointBlockSumEquiv_apply_norm_le B hB hP h hh h0)

theorem ordinalPrincipalOmegaEndpointBlockSumEquiv_symm_norm_le (B : Ordinal.{u}) (hB : Ordinal.omega0 < B) (hP : Ordinal.Principal (· + ·) B) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    ‖(ordinalPrincipalOmegaEndpointBlockSumEquiv (𝕜 := 𝕜) B hB hP h hh h0).symm.toContinuousLinearMap‖ ≤ 8 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalPrincipalOmegaEndpointBlockSumEquiv_symm_apply_norm_le B hB hP h hh h0)

end Posets


