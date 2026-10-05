import JLMS.OrdinalSpaceSingularBlocks
import JLMS.CZeroSumOrdinalReplication

/-!
# Singular initial ordinal spaces are isomorphic to their squares

Consecutive successor-cardinal blocks absorb cofinality-many copies of the
previous block, with one common distortion bound. Splitting the index ordinal
into consecutive ω-blocks gives replication of the whole block sum. Together
with the concrete block decomposition this supplies the singular branch of
the classification used in Section 9.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance singularReplicationFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance singularReplicationFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance singularReplicationEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularReplicationEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

theorem nonempty_singularCardinalBlockSumSquare {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) :
    Nonempty (singularCardinalBlockSum 𝕜 c ≃L[𝕜]
      singularCardinalBlockSum 𝕜 c × singularCardinalBlockSum 𝕜 c) := by
  letI := ordinalIioInfinite c.ord.cof.ord (omega0_le_singularCardinal_cofinality hc)
  exact nonempty_cZeroSum_ordinalSquare c.ord.cof.ord
    (Cardinal.isSuccLimit_ord (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc)))
    (Set.Iio c.ord.cof.ord)
    (fun ξ : Set.Iio c.ord.cof.ord => ordinalEndpointZero 𝕜
      (singularCardinalSequence c (Order.succ ξ.val)))
    (by norm_num : (0 : ℝ) ≤ 1024)
    (fun ξ => exists_singularCardinal_adjacent_absorption (𝕜 := 𝕜) hc ξ.val)

def ordinalEndpointZeroSingularInitialSquareEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      ordinalEndpointZero 𝕜 c.ord × ordinalEndpointZero 𝕜 c.ord :=
  let d := ordinalEndpointZeroSingularBlockSumEquiv (𝕜 := 𝕜) hc hs
  let e := Classical.choice (nonempty_singularCardinalBlockSumSquare (𝕜 := 𝕜) hc)
  d.trans (e.trans (d.symm.prodCongr d.symm))

/-- The square equivalence for every singular infinite initial ordinal. -/
def ordinalSpaceSingularInitialSquareEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    OrdinalC 𝕜 c.ord ≃L[𝕜] OrdinalC 𝕜 c.ord × OrdinalC 𝕜 c.ord :=
  let hω : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  let d := ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) c.ord hω
  d.trans ((ordinalEndpointZeroSingularInitialSquareEquiv (𝕜 := 𝕜) c hc hs).trans
    (d.symm.prodCongr d.symm))

end JLMS
