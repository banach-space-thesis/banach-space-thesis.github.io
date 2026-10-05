import Posets.OrdinalRegularOmegaBlockModelGeometry
import Posets.OrdinalRegularOmegaBlockModelNorms
import JLMS.OrdinalSpacePowerSuccessor

/-! The actual endpoint-zero space at κ^ω is uniformly equivalent to the
c₀ sum along any strictly increasing positive finite heights. -/

noncomputable section
open Set Order
namespace Posets
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance omegaBlockModelEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaBlockModelEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance omegaBlockModelSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance omegaBlockModelSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

def ordinalOmegaBlockCoordinatesIsometry (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.CZeroSum 𝕜 (fun ξ : Iio (Ordinal.omega0 : Ordinal.{u}) =>
      JLMS.ordinalEndpointZero 𝕜 (JLMS.ordinalSpaceBlockLength
        (ordinalOmegaBlockMap c.ord
          (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) h hh h0) ξ)) ≃ₗᵢ[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (JLMS.CZeroSum.reindex (𝕜 := 𝕜) ordinalOmegaNatIndexEquiv).trans
    (JLMS.CZeroSum.congrRightIsometry (fun n => JLMS.ordinalEndpointZeroCongrIsometry
      (ordinalOmegaBlockMap_length c hc h hh h0 n)))

def ordinalOmegaEndpointSplit (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
        JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (JLMS.ordinalEndpointZeroBlocksEquiv
    (ordinalOmegaBlockMap c.ord
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0)
    (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0)
    (ordinalOmegaBlockMap_infinite_blocks c hc h hh h0)).trans
    ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
      (ordinalOmegaBlockCoordinatesIsometry c hc h hh h0).toContinuousLinearEquiv)

theorem ordinalOmegaEndpointSplit_norm_le (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0)) :
    ‖ordinalOmegaEndpointSplit c hc h hh h0 x‖ ≤ 2 * ‖x‖ := by
  let d := ordinalOmegaBlockCoordinatesIsometry (𝕜 := 𝕜) c hc h hh h0
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalOmegaBlockMap c.ord
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0) (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0) (ordinalOmegaBlockMap_infinite_blocks c hc h hh h0)
  change max ‖(e x).1‖ ‖d (e x).2‖ ≤ _
  rw [d.norm_map]
  exact JLMS.norm_ordinalEndpointZeroBlocksEquiv_apply_le _ _ _ _ _ x

theorem ordinalOmegaEndpointSplit_symm_norm_le (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 1 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)))) :
    ‖(ordinalOmegaEndpointSplit c hc h hh h0).symm x‖ ≤ 2 * ‖x‖ := by
  let d := ordinalOmegaBlockCoordinatesIsometry (𝕜 := 𝕜) c hc h hh h0
  let e := JLMS.ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (ordinalOmegaBlockMap c.ord
      (Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)) h hh h0)
    (ordinalOmegaBlockMap_strictMono _ _ h hh h0) (ordinalOmegaBlockMap_zero _ _ h hh h0)
    (ordinalOmegaBlockMap_endpoint _ _ h hh h0) (ordinalOmegaBlockMap_infinite_blocks c hc h hh h0)
  change ‖e.symm (x.1, d.symm x.2)‖ ≤ _
  calc
    _ ≤ 2 * ‖(x.1, d.symm x.2)‖ := JLMS.norm_ordinalEndpointZeroBlocksEquiv_symm_apply_le _ _ _ _ _ _
    _ = 2 * ‖x‖ := by simp only [Prod.norm_def, d.symm.norm_map]

theorem ordinalOmegaBlock_head_absorption (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (h0 : 2 ≤ h 0) :
    Ordinal.omega0 + c.ord ^ (h 0 : Ordinal) = c.ord ^ (h 0 : Ordinal) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have he : (1 : Ordinal.{u}) < (h 0 : Ordinal) := by exact_mod_cast (by omega : 1 < h 0)
  have ht : c.ord < c.ord ^ (h 0 : Ordinal) := by
    simpa only [Ordinal.opow_one] using (Ordinal.opow_lt_opow_iff_right hκ).mpr he
  exact Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _)
    _ ((Cardinal.omega0_le_ord.mpr hc).trans_lt ht)

def ordinalOmegaBlockHeadAbsorption (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (h0 : 2 ≤ h 0) :
    (JLMS.ordinalEndpointZero 𝕜 (Ordinal.omega0 : Ordinal.{u}) ×
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h 0 : Ordinal))) ≃L[𝕜]
      JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h 0 : Ordinal)) :=
  JLMS.ordinalEndpointZeroAbsorbLeft _ _ le_rfl
    (JLMS.ordinalInitialPower_infinite c hc _ (by exact_mod_cast (by omega : 1 ≤ h 0)))
    (ordinalOmegaBlock_head_absorption c hc h h0)

def ordinalOmegaEndpointBlockSumEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) :=
  (ordinalOmegaEndpointSplit c hc h hh (by omega)).trans
    (JLMS.cZeroSumAbsorbsAt (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)))
      0 (ordinalOmegaBlockHeadAbsorption c hc h h0))

theorem ordinalOmegaBlockHeadAbsorption_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (h0 : 2 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h 0 : Ordinal))) :
    ‖(ordinalOmegaBlockHeadAbsorption c hc h h0).symm x‖ ≤ 4 * ‖x‖ :=
  JLMS.norm_ordinalEndpointZeroAbsorbLeft_symm_le Ordinal.omega0
    (c.ord ^ (h 0 : Ordinal)) le_rfl
    (JLMS.ordinalInitialPower_infinite c hc _ (by exact_mod_cast (by omega : 1 ≤ h 0)))
    (ordinalOmegaBlock_head_absorption c hc h h0) x

theorem ordinalOmegaEndpointBlockSumEquiv_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.ordinalEndpointZero 𝕜 (c.ord ^ Ordinal.omega0)) :
    ‖ordinalOmegaEndpointBlockSumEquiv c hc h hh h0 x‖ ≤ 8 * ‖x‖ := by
  have hn := ordinalOmegaBlock_absorbsAt_norm_le
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) 0
    (ordinalOmegaBlockHeadAbsorption c hc h h0) (C := 4) (by norm_num)
    (JLMS.norm_ordinalEndpointZeroAbsorbLeft_le _ _ _ _ _)
    (ordinalOmegaEndpointSplit c hc h hh (by omega) x)
  have hs := ordinalOmegaEndpointSplit_norm_le c hc h hh (by omega) x
  exact hn.trans (by linarith)

theorem ordinalOmegaEndpointBlockSumEquiv_symm_apply_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0)
    (x : JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)))) :
    ‖(ordinalOmegaEndpointBlockSumEquiv c hc h hh h0).symm x‖ ≤ 8 * ‖x‖ := by
  let a := JLMS.cZeroSumAbsorbsAt
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal)))
    0 (ordinalOmegaBlockHeadAbsorption c hc h h0)
  have hn := ordinalOmegaBlock_absorbsAt_symm_norm_le
    (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜 (c.ord ^ (h n : Ordinal))) 0
    (ordinalOmegaBlockHeadAbsorption c hc h h0) (C := 4) (by norm_num)
    (ordinalOmegaBlockHeadAbsorption_symm_norm_le c hc h h0) x
  have hs := ordinalOmegaEndpointSplit_symm_norm_le c hc h hh (by omega) (a.symm x)
  exact hs.trans (by linarith)

theorem ordinalOmegaEndpointBlockSumEquiv_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaEndpointBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).toContinuousLinearMap‖ ≤ 8 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalOmegaEndpointBlockSumEquiv_apply_norm_le c hc h hh h0)

theorem ordinalOmegaEndpointBlockSumEquiv_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (h : ℕ → ℕ) (hh : StrictMono h) (h0 : 2 ≤ h 0) :
    ‖(ordinalOmegaEndpointBlockSumEquiv (𝕜 := 𝕜) c hc h hh h0).symm.toContinuousLinearMap‖ ≤ 8 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (ordinalOmegaEndpointBlockSumEquiv_symm_apply_norm_le c hc h hh h0)

end Posets
