import JLMS.OrdinalSpaceMultipleSum
import JLMS.CZeroSumReplication
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Successor powers in Kislyakov Lemma 3.2

For an infinite initial ordinal κ and β≥1, the space at κ^(β+1) is
the c₀ sum of κ copies of the space at κ^β. Repeating the index set
therefore makes κ^(β+1) isomorphic to κ copies of itself. The norm
bounds are uniform in β, which is essential in the limit-exponent case.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance powerSuccessorFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance powerSuccessorFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance powerSuccessorEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerSuccessorEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerSuccessorSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance powerSuccessorSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

theorem ordinalInitialPower_infinite (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{u}) (hβ : 1 ≤ β) : Ordinal.omega0 ≤ c.ord ^ β := by
  have hκ : Ordinal.omega0 ≤ c.ord := by simpa using Cardinal.ord_le_ord.mpr hc
  exact hκ.trans (by simpa only [Ordinal.opow_one] using
    Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le hκ) hβ)

theorem ordinalInitialPower_baseAbsorption (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{u}) (hβ : 1 ≤ β) :
    c.ord = c.ord ^ β ∨ c.ord + c.ord ^ β = c.ord ^ β := by
  by_cases he : β = 1
  · subst β
    exact Or.inl (Ordinal.opow_one _).symm
  · right
    have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le
      (by simpa using Cardinal.ord_le_ord.mpr hc)
    have hlt : c.ord < c.ord ^ β := by
      simpa only [Ordinal.opow_one] using
        (Ordinal.opow_lt_opow_iff_right hκ).mpr (lt_of_le_of_ne hβ (Ne.symm he))
    exact Ordinal.principal_add_iff_add_left_eq_self.mp
      (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) β) _ hlt

def ordinalEndpointZeroPowerSuccessorSum (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{u}) (hβ : 1 ≤ β) :
    ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ β)) :=
  (ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) (Ordinal.opow_succ c.ord β)).toContinuousLinearEquiv.trans
    (ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) (c.ord ^ β) c.ord
      (ordinalInitialPower_infinite c hc β hβ)
      (by simpa using Cardinal.ord_le_ord.mpr hc) (ordinalInitialPower_baseAbsorption c hc β hβ))

theorem norm_ordinalEndpointZeroPowerSuccessorSum_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β)
    (f : ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β)) :
    ‖ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ f‖ ≤ 8 * ‖f‖ := by
  let e := ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) (Ordinal.opow_succ c.ord β)
  have h := norm_ordinalEndpointZeroMultipleSumEquiv_le
    (c.ord ^ β) c.ord (ordinalInitialPower_infinite c hc β hβ)
    (by simpa using Cardinal.ord_le_ord.mpr hc) (ordinalInitialPower_baseAbsorption c hc β hβ) (e f)
  rw [e.norm_map] at h
  exact h

theorem norm_ordinalEndpointZeroPowerSuccessorSum_symm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β)
    (f : CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ β))) :
    ‖(ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).symm f‖ ≤ 8 * ‖f‖ := by
  change ‖(ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) (Ordinal.opow_succ c.ord β)).symm
    ((ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) (c.ord ^ β) c.ord _ _ _).symm f)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_ordinalEndpointZeroMultipleSumEquiv_symm_le _ _ _ _ _ f

def ordinalEndpointZeroPowerSuccessorReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β) :
    ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β)) := by
  letI := ordinalIioInfinite c.ord (by simpa using Cardinal.ord_le_ord.mpr hc)
  exact CZeroSum.replicationOfEquiv (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ)

theorem ordinalEndpointZeroPowerSuccessorSum_distortion_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β) :
    ‖(ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).toContinuousLinearMap‖ *
      ‖(ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).symm.toContinuousLinearMap‖ ≤ 64 := by
  have h₁ := ContinuousLinearMap.opNorm_le_bound
    (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).toContinuousLinearMap
    (by norm_num : (0 : ℝ) ≤ 8) (norm_ordinalEndpointZeroPowerSuccessorSum_le c hc β hβ)
  have h₂ := ContinuousLinearMap.opNorm_le_bound
    (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).symm.toContinuousLinearMap
    (by norm_num : (0 : ℝ) ≤ 8) (norm_ordinalEndpointZeroPowerSuccessorSum_symm_le c hc β hβ)
  nlinarith [norm_nonneg (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).toContinuousLinearMap,
    norm_nonneg (ordinalEndpointZeroPowerSuccessorSum (𝕜 := 𝕜) c hc β hβ).symm.toContinuousLinearMap]

theorem norm_ordinalEndpointZeroPowerSuccessorReplication_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β)
    (f : ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β)) :
    ‖ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc β hβ f‖ ≤ 64 * ‖f‖ := by
  letI := ordinalIioInfinite c.ord (by simpa using Cardinal.ord_le_ord.mpr hc)
  exact (CZeroSum.norm_replicationOfEquiv_apply_le _ f).trans
    (mul_le_mul_of_nonneg_right (ordinalEndpointZeroPowerSuccessorSum_distortion_le (𝕜 := 𝕜) c hc β hβ)
      (norm_nonneg f))

theorem norm_ordinalEndpointZeroPowerSuccessorReplication_symm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (β : Ordinal.{u}) (hβ : 1 ≤ β)
    (f : CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ Order.succ β))) :
    ‖(ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc β hβ).symm f‖ ≤ 64 * ‖f‖ := by
  letI := ordinalIioInfinite c.ord (by simpa using Cardinal.ord_le_ord.mpr hc)
  exact (CZeroSum.norm_replicationOfEquiv_symm_apply_le _ f).trans
    (mul_le_mul_of_nonneg_right (ordinalEndpointZeroPowerSuccessorSum_distortion_le (𝕜 := 𝕜) c hc β hβ)
      (norm_nonneg f))

end JLMS
