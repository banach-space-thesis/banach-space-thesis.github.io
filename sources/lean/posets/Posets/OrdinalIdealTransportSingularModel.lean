import JLMS.OrdinalSpaceSingularBlocks
import Posets.OrdinalIdealTransportRegularQuantitative
import JLMS.CZeroSumOperators

/-! The singular initial C-space as the actual c₀ sum of full regular initial
C-spaces. The coordinate changes use the uniform endpoint-zero bounds. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

local instance singularModelFunctionGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance singularModelFunctionSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance singularModelEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularModelEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def singularRegularCardinal (c : Cardinal.{0}) (i : Set.Iio c.ord.cof.ord) : Cardinal.{0} :=
  (singularCardinalSequence c (Order.succ i.val)).card

theorem singularRegularCardinal_ord {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (i : Set.Iio c.ord.cof.ord) :
    (singularRegularCardinal c i).ord = singularCardinalSequence c (Order.succ i.val) := by
  obtain ⟨d, _, he, _⟩ := singularCardinalSequence_succ_regular hc i.val
  simp only [singularRegularCardinal, he, Cardinal.card_ord]

theorem singularRegularCardinal_regular {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (i : Set.Iio c.ord.cof.ord) : (singularRegularCardinal c i).IsRegular := by
  obtain ⟨d, _, he, hd⟩ := singularCardinalSequence_succ_regular hc i.val
  simpa only [singularRegularCardinal, he, Cardinal.card_ord] using hd

theorem singularRegularCardinal_uncountable {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (i : Set.Iio c.ord.cof.ord) : Cardinal.aleph0 < singularRegularCardinal c i := by
  obtain ⟨d, hd, he, _⟩ := singularCardinalSequence_succ_regular hc i.val
  simpa only [singularRegularCardinal, he, Cardinal.card_ord] using hd.trans_lt (Order.lt_succ d)

theorem singularRegularCardinal_strictMono {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c) :
    StrictMono (singularRegularCardinal c) := by
  intro i j hij
  apply Cardinal.ord_lt_ord.mp
  rw [singularRegularCardinal_ord hc i, singularRegularCardinal_ord hc j]
  exact (isNormal_singularCardinalSequence c).strictMono (Order.succ_lt_succ hij)

theorem singularRegularCardinal_index_small {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (i : Set.Iio c.ord.cof.ord) : i.val.card < singularRegularCardinal c i := by
  apply Cardinal.lt_ord.mp
  rw [singularRegularCardinal_ord hc i]
  exact i.property.trans (singularCardinalSequence_succ_gt c i.val)

def ordinalSingularRegularSumEquiv {c : Cardinal.{0}} (hc : Cardinal.aleph0 ≤ c)
    (hs : ¬ c.IsRegular) :
    OrdinalC 𝕜 c.ord ≃L[𝕜]
      CZeroSum 𝕜 (fun i : Set.Iio c.ord.cof.ord =>
        OrdinalC 𝕜 (singularCardinalSequence c (Order.succ i.val))) := by
  let e (i : Set.Iio c.ord.cof.ord) := ordinalSpaceEndpointZeroBoundedEquiv
    (𝕜 := 𝕜) (singularCardinalSequence c (Order.succ i.val))
    (omega0_le_singularCardinalSequence_succ hc i.val)
  have he (i : Set.Iio c.ord.cof.ord) : ‖(e i).toContinuousLinearMap‖ ≤ 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalSpaceEndpointZeroBoundedEquiv_le _ _)
  have hei (i : Set.Iio c.ord.cof.ord) : ‖(e i).symm.toContinuousLinearMap‖ ≤ 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le _ _)
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  exact (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord hκ).trans
    ((ordinalEndpointZeroSingularBlockSumEquiv (𝕜 := 𝕜) hc hs).trans
      (CZeroSum.congrRight (fun i => (e i).symm) (by norm_num) (by norm_num) hei he))

end Posets
