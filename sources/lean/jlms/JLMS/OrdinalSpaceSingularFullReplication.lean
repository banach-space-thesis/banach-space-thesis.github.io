import JLMS.OrdinalSpaceSingularReplication
import JLMS.CZeroSumReplicationFromBlocks

/-!
# Kislyakov Lemma 3.3: replication by the whole singular cardinal

The cofinality-indexed adjacent absorption gives the first replication.
For each smaller block δ, the normal map ξ ↦ δξ decomposes the full space
into itself and c-many copies of that block. Summing these decompositions
and interchanging the two c₀ indices gives the full c-fold replication.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance singularFullFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance singularFullFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance singularFullEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularFullEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularFullSumGroup (α β : Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) :=
  inferInstance
local instance singularFullSumSpace (α β : Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) :=
  inferInstance
local instance singularFullProdGroup (α β γ : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 γ ×
      CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) := inferInstance
local instance singularFullProdSpace (α β γ : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 γ ×
      CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) := inferInstance

def ordinalEndpointZeroSingularCofinalityReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord.cof.ord => ordinalEndpointZero 𝕜 c.ord) := by
  letI := ordinalIioInfinite c.ord.cof.ord (omega0_le_singularCardinal_cofinality hc)
  let d := ordinalEndpointZeroSingularBlockSumEquiv (𝕜 := 𝕜) hc hs
  let e := Classical.choice (nonempty_cZeroSum_ordinalReplication c.ord.cof.ord
    (Cardinal.isSuccLimit_ord (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc)))
    (Set.Iio c.ord.cof.ord)
    (fun ξ : Set.Iio c.ord.cof.ord => ordinalEndpointZero 𝕜
      (singularCardinalSequence c (Order.succ ξ.val)))
    (by norm_num : (0 : ℝ) ≤ 1024)
    (fun ξ => exists_singularCardinal_adjacent_absorption (𝕜 := 𝕜) hc ξ.val))
  exact d.trans (e.trans (CZeroSum.congrRight (fun _ : Set.Iio c.ord.cof.ord => d.symm)
    d.symm.toContinuousLinearMap.opNorm_nonneg d.toContinuousLinearMap.opNorm_nonneg
    (fun _ => le_rfl) (fun _ => le_rfl)))

theorem singularCardinalSequence_succ_mul_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    singularCardinalSequence c (Order.succ ξ.val) * c.ord = c.ord := by
  apply Ordinal.principal_mul_iff_mul_left_eq.mp (Ordinal.principal_mul_ord hc)
  · exact Ordinal.omega0_pos.trans_le (omega0_le_singularCardinalSequence_succ hc ξ.val)
  · exact singularCardinalSequence_lt hc hs
      ((Cardinal.isSuccLimit_ord
        (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc))).succ_lt ξ.prop)

def ordinalEndpointZeroSingularBlockExpansion (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      ordinalEndpointZero 𝕜 c.ord × CZeroSum 𝕜 (fun _ : Set.Iio c.ord =>
        ordinalEndpointZero 𝕜 (singularCardinalSequence c (Order.succ ξ.val))) :=
  (ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (singularCardinalSequence_succ_mul_endpoint hc hs ξ).symm).toContinuousLinearEquiv.trans
      (ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜)
        (singularCardinalSequence c (Order.succ ξ.val)) c.ord
        (omega0_le_singularCardinalSequence_succ hc ξ.val))

theorem ordinalEndpointZeroSingularBlockExpansion_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    ‖(ordinalEndpointZeroSingularBlockExpansion (𝕜 := 𝕜) c hc hs ξ).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  let d := ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (singularCardinalSequence_succ_mul_endpoint hc hs ξ).symm
  exact (norm_ordinalEndpointZeroMultipleBlocksEquiv_le (𝕜 := 𝕜)
    (singularCardinalSequence c (Order.succ ξ.val)) c.ord
    (omega0_le_singularCardinalSequence_succ hc ξ.val) (d f)).trans_eq
    (congrArg (fun r : ℝ => 2 * r) (d.norm_map f))

theorem ordinalEndpointZeroSingularBlockExpansion_symm_norm_le (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    ‖(ordinalEndpointZeroSingularBlockExpansion (𝕜 := 𝕜) c hc hs ξ).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  let d := ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (singularCardinalSequence_succ_mul_endpoint hc hs ξ).symm
  change ‖d.symm ((ordinalEndpointZeroMultipleBlocksEquiv (𝕜 := 𝕜)
    (singularCardinalSequence c (Order.succ ξ.val)) c.ord
    (omega0_le_singularCardinalSequence_succ hc ξ.val)).symm f)‖ ≤ _
  rw [d.symm.norm_map]
  exact norm_ordinalEndpointZeroMultipleBlocksEquiv_symm_le _ _ _ f

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Kislyakov Lemma 3.3 for every singular infinite cardinal, including
singular fixed points of the aleph function. -/
def ordinalEndpointZeroSingularInitialReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 c.ord) := by
  have hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  letI := ordinalIioInfinite c.ord hω
  apply Classical.choice (nonempty_cZeroSum_replicationFromBlocks (𝕜 := 𝕜)
    (Set.Iio c.ord)
    (fun ξ : Set.Iio c.ord.cof.ord => ordinalEndpointZero 𝕜
      (singularCardinalSequence c (Order.succ ξ.val)))
    (ordinalEndpointZeroSingularBlockSumEquiv (𝕜 := 𝕜) hc hs)
    (ordinalEndpointZeroSingularCofinalityReplication (𝕜 := 𝕜) c hc hs)
    (by norm_num : (0 : ℝ) ≤ 4) ?_)
  intro ξ
  let e := ordinalEndpointZeroSingularBlockExpansion (𝕜 := 𝕜) c hc hs ξ
  refine ⟨e, ?_⟩
  exact (mul_le_mul (ordinalEndpointZeroSingularBlockExpansion_norm_le c hc hs ξ)
    (ordinalEndpointZeroSingularBlockExpansion_symm_norm_le c hc hs ξ)
    e.symm.toContinuousLinearMap.opNorm_nonneg (by norm_num)).trans_eq (by norm_num)

end JLMS
