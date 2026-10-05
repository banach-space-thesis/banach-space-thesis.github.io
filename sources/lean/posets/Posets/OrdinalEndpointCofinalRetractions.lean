import Posets.OrdinalEndpointRetractions
import JLMS.CZeroSumOperators

/-! Uniformly complemented initial-segment block families. Applied to a
coordinatewise larger cofinal subfamily, these are the genuine maps that
recover the whole varying c₀ sum. No isomorphism or factorisation property
is posited for the sum. -/
noncomputable section
namespace Posets
open JLMS
universe u v
variable {𝕜 : Type*} [RCLike 𝕜] {I : Type v}
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance cofinalRetractionFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance cofinalRetractionFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance cofinalRetractionEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance cofinalRetractionEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance cofinalRetractionSumGroup (α : I → Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance
local instance cofinalRetractionSumSpace (α : I → Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance

def ordinalEndpointFamilyExtend (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i) :
    CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)) →L[𝕜]
      CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (β i)) :=
  CZeroSum.mapCLM (fun i => ordinalEndpointExtend (𝕜 := 𝕜) (α i) (β i) (h i))
    zero_le_one (fun i => norm_ordinalEndpointExtend_le (𝕜 := 𝕜) (α i) (β i) (h i))

def ordinalEndpointFamilyRead (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i) :
    CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (β i)) →L[𝕜]
      CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i)) :=
  CZeroSum.mapCLM (fun i => ordinalEndpointRead (𝕜 := 𝕜) (α i) (β i) (h i))
    (by norm_num : (0 : ℝ) ≤ 2) (fun i => norm_ordinalEndpointRead_le (𝕜 := 𝕜) (α i) (β i) (h i))

@[simp] theorem ordinalEndpointFamilyExtend_apply (α β : I → Ordinal.{u})
    (h : ∀ i, α i ≤ β i) (x : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) (i : I) :
    ordinalEndpointFamilyExtend (𝕜 := 𝕜) α β h x i =
      ordinalEndpointExtend (𝕜 := 𝕜) (α i) (β i) (h i) (x i) := rfl

@[simp] theorem ordinalEndpointFamilyRead_apply (α β : I → Ordinal.{u})
    (h : ∀ i, α i ≤ β i) (x : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (β i))) (i : I) :
    ordinalEndpointFamilyRead (𝕜 := 𝕜) α β h x i =
      ordinalEndpointRead (𝕜 := 𝕜) (α i) (β i) (h i) (x i) := rfl

theorem norm_ordinalEndpointFamilyExtend_le (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i) :
    ‖ordinalEndpointFamilyExtend (𝕜 := 𝕜) α β h‖ ≤ 1 :=
  CZeroSum.norm_mapCLM_le _ _ _

theorem norm_ordinalEndpointFamilyRead_le (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i) :
    ‖ordinalEndpointFamilyRead (𝕜 := 𝕜) α β h‖ ≤ 2 :=
  CZeroSum.norm_mapCLM_le _ _ _

theorem ordinalEndpointFamilyRead_comp_extend (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i) :
    (ordinalEndpointFamilyRead (𝕜 := 𝕜) α β h).comp (ordinalEndpointFamilyExtend α β h) =
      ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := by
  apply ContinuousLinearMap.ext
  intro x
  apply CZeroSum.ext
  intro i
  exact ordinalEndpointRead_extend (𝕜 := 𝕜) (α i) (β i) (h i) (x i)

theorem norm_ordinalEndpointFamilyExtend (α β : I → Ordinal.{u}) (h : ∀ i, α i ≤ β i)
    (x : CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) :
    ‖ordinalEndpointFamilyExtend (𝕜 := 𝕜) α β h x‖ = ‖x‖ := by
  apply le_antisymm
  · apply ((ordinalEndpointFamilyExtend (𝕜 := 𝕜) α β h).le_opNorm x).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (norm_ordinalEndpointFamilyExtend_le (𝕜 := 𝕜) α β h) (norm_nonneg x)
  · apply CZeroSum.norm_le (norm_nonneg _)
    intro i
    have hi := (ordinalEndpointFamilyExtend (𝕜 := 𝕜) α β h x).norm_apply_le_norm i
    rwa [ordinalEndpointFamilyExtend_apply, norm_ordinalEndpointExtend] at hi

end Posets
