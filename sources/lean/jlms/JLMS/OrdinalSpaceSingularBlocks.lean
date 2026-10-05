import JLMS.OrdinalSpaceSingularSequence
import JLMS.OrdinalSpaceSumFactorAbsorption
import JLMS.CZeroSumCoordinateAbsorption

/-!
# The varying block sum at a singular initial ordinal

The cofinality summand in the ceiling-retraction decomposition is absorbed
into the first successor-cardinal block. Consecutive blocks have uniformly
bounded absorptions of cofinality-many copies of the preceding block.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance singularBlocksFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance singularBlocksFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance singularBlocksEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularBlocksEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularBlocksSumGroup (α β : Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) :=
  inferInstance
local instance singularBlocksSumSpace (α β : Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α)) :=
  inferInstance
local instance singularBlocksProdGroup (α β γ : Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α) ×
      ordinalEndpointZero 𝕜 γ) := inferInstance
local instance singularBlocksProdSpace (α β γ : Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun _ : Set.Iio β => ordinalEndpointZero 𝕜 α) ×
      ordinalEndpointZero 𝕜 γ) := inferInstance

theorem omega0_le_singularCardinal_cofinality {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) : Ordinal.omega0 ≤ c.ord.cof.ord := by
  simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr
    (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc))

theorem omega0_le_singularCardinalSequence_succ {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (ν : Ordinal.{u}) :
    Ordinal.omega0 ≤ singularCardinalSequence c (Order.succ ν) :=
  (omega0_le_singularCardinal_cofinality hc).trans (singularCardinalSequence_succ_gt c ν).le

theorem add_singularCardinalSequence_succ {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (ν : Ordinal.{u}) {η : Ordinal.{u}}
    (hη : η < singularCardinalSequence c (Order.succ ν)) :
    η + singularCardinalSequence c (Order.succ ν) =
      singularCardinalSequence c (Order.succ ν) := by
  obtain ⟨d, hd, he, _⟩ := singularCardinalSequence_succ_regular hc ν
  rw [he] at hη ⊢
  exact (Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_ord (hd.trans (Order.le_succ _)))) η hη

def singularCardinalBlockSum (𝕜 : Type*) [RCLike 𝕜] (c : Cardinal.{u}) :=
  CZeroSum 𝕜 (fun ξ : Set.Iio c.ord.cof.ord =>
    ordinalEndpointZero 𝕜 (singularCardinalSequence c (Order.succ ξ.val)))

instance (c : Cardinal.{u}) : NormedAddCommGroup (singularCardinalBlockSum 𝕜 c) :=
  inferInstanceAs (NormedAddCommGroup (CZeroSum 𝕜 _))
instance (c : Cardinal.{u}) : NormedSpace 𝕜 (singularCardinalBlockSum 𝕜 c) :=
  inferInstanceAs (NormedSpace 𝕜 (CZeroSum 𝕜 _))

def singularCardinalBlockLengthIsometry {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    CZeroSum 𝕜 (fun ξ : Set.Iio c.ord.cof.ord =>
      ordinalEndpointZero 𝕜 (ordinalSpaceBlockLength (singularCardinalSequenceMap hc hs) ξ))
      ≃ₗᵢ[𝕜] singularCardinalBlockSum 𝕜 c :=
  CZeroSum.congrRightIsometry (fun ξ =>
    ordinalEndpointZeroCongrIsometry (singularCardinalSequenceMap_blockLength hc hs ξ))

/-- Singular initial spaces are the c₀ sum of their successor-cardinal blocks. -/
def ordinalEndpointZeroSingularBlockSumEquiv {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜] singularCardinalBlockSum 𝕜 c := by
  let hκ := omega0_le_singularCardinal_cofinality hc
  let i : Set.Iio c.ord.cof.ord := ⟨0, Ordinal.omega0_pos.trans_le hκ⟩
  let h := ordinalEndpointZeroAbsorbLeft (𝕜 := 𝕜) c.ord.cof.ord
    (singularCardinalSequence c (Order.succ i.val)) hκ
    (omega0_le_singularCardinalSequence_succ hc i.val)
    (add_singularCardinalSequence_succ hc i.val (singularCardinalSequence_succ_gt c i.val))
  exact (ordinalEndpointZeroBlocksEquiv (𝕜 := 𝕜)
    (singularCardinalSequenceMap hc hs) (strictMono_singularCardinalSequenceMap hc hs)
    (singularCardinalSequenceMap_zero hc hs) (singularCardinalSequenceMap_endpoint hc hs)
    (singularCardinalSequenceMap_blockLength_infinite hc hs)).trans
      (((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
        (singularCardinalBlockLengthIsometry (𝕜 := 𝕜) hc hs).toContinuousLinearEquiv).trans
          (cZeroSumAbsorbsAt _ i h))

theorem singularCardinalSequence_adjacent_factor {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (ν : Ordinal.{u}) :
    singularCardinalSequence c (Order.succ ν) * c.ord.cof.ord +
      singularCardinalSequence c (Order.succ (Order.succ ν)) =
        singularCardinalSequence c (Order.succ (Order.succ ν)) := by
  apply add_singularCardinalSequence_succ hc
  obtain ⟨d, hd, he, _⟩ := singularCardinalSequence_succ_regular hc (Order.succ ν)
  have hsmall := (isNormal_singularCardinalSequence c).strictMono (Order.lt_succ (Order.succ ν))
  have hcf := singularCardinalSequence_succ_gt c (Order.succ ν)
  rw [he] at hsmall hcf ⊢
  exact (Ordinal.principal_mul_ord (hd.trans (Order.le_succ d))) hsmall hcf

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Uniform adjacent absorption, the Banach-space input to Lemma 3.3. -/
theorem exists_singularCardinal_adjacent_absorption {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (ν : Ordinal.{u}) :
    ∃ e : ordinalEndpointZero 𝕜 (singularCardinalSequence c (Order.succ (Order.succ ν))) ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord.cof.ord =>
        ordinalEndpointZero 𝕜 (singularCardinalSequence c (Order.succ ν))) ×
          ordinalEndpointZero 𝕜 (singularCardinalSequence c (Order.succ (Order.succ ν))),
      ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ≤ 1024 := by
  let e := ordinalEndpointZeroSumFactorAbsorption (𝕜 := 𝕜)
    (singularCardinalSequence c (Order.succ ν)) c.ord.cof.ord
    (singularCardinalSequence c (Order.succ (Order.succ ν)))
    (omega0_le_singularCardinalSequence_succ hc ν) (omega0_le_singularCardinal_cofinality hc)
    (omega0_le_singularCardinalSequence_succ hc (Order.succ ν))
    (Or.inr (add_singularCardinalSequence_succ hc ν (singularCardinalSequence_succ_gt c ν)))
    (singularCardinalSequence_adjacent_factor hc ν)
  refine ⟨e, ?_⟩
  have hf : ‖e.toContinuousLinearMap‖ ≤ 32 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalEndpointZeroSumFactorAbsorption_le _ _ _ _ _ _ _ _)
  have hg : ‖e.symm.toContinuousLinearMap‖ ≤ 32 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalEndpointZeroSumFactorAbsorption_symm_le _ _ _ _ _ _ _ _)
  exact (mul_le_mul hf hg e.symm.toContinuousLinearMap.opNorm_nonneg
    (by norm_num)).trans_eq (by norm_num)

end JLMS
