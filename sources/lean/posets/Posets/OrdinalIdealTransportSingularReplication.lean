import Posets.OrdinalIdealTransportSingularFactorization
import Posets.OrdinalIdealTransportSmallQuotient
import JLMS.OrdinalSpaceSingularFullReplication

/-! Singular initial spaces replicate over every smaller infinite index set.
The construction uses the actual full singular replication and c₀ Fubini. -/
noncomputable section
namespace Posets
open JLMS
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance smallerReplicationSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance smallerReplicationSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance
local instance smallerReplicationEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance smallerReplicationEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

/-- Full replication implies replication over every smaller infinite set. -/
def cZeroSum_smallerReplication {I J : Type u} [Infinite I] [Infinite J]
    {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hJI : Cardinal.mk J ≤ Cardinal.mk I)
    (e : X ≃L[𝕜] CZeroSum 𝕜 (fun _ : I => X)) :
    X ≃L[𝕜] CZeroSum 𝕜 (fun _ : J => X) := by
  have hcard : Cardinal.mk (J × I) = Cardinal.mk I := by
    simp only [Cardinal.mk_prod, Cardinal.lift_id]
    exact (Cardinal.mul_eq_max (Cardinal.aleph0_le_mk J) (Cardinal.aleph0_le_mk I)).trans
      (max_eq_right hJI)
  let r : J × I ≃ I := Classical.choice (Cardinal.eq.mp hcard)
  exact e.trans ((CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : I => X) r).toContinuousLinearEquiv.trans
    ((CZeroSum.prodIsometry (𝕜 := 𝕜) (E := fun _ : J => fun _ : I => X)).symm.toContinuousLinearEquiv.trans
      (CZeroSum.congrRight (fun _ : J => e.symm) (norm_nonneg _) (norm_nonneg _)
        (fun _ => le_rfl) (fun _ => le_rfl))))

def singularEndpointSmallerReplication {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (γ : Ordinal.{0}) (hγ : Ordinal.omega0 ≤ γ) (hγc : γ.card ≤ c) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : γ.toType => ordinalEndpointZero 𝕜 c.ord) := by
  letI : Infinite c.ord.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hc)
  letI : Infinite γ.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Ordinal.card_omega0] using Ordinal.card_le_card hγ)
  let e := (ordinalEndpointZeroSingularInitialReplication (𝕜 := 𝕜) c hc hs).trans
    (CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 c.ord)
      (Ordinal.enumIsoToType c.ord).symm.toEquiv).toContinuousLinearEquiv
  exact cZeroSum_smallerReplication
    (by simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hγc) e

def singularInitialInfiniteQuotientEquiv {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (α : Ordinal.{0}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 c.ord := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  have hγ := initialInfiniteQuotient_omega_le c hc α hlo
  have hγc : (α / c.ord).card ≤ c := by
    simpa only [Cardinal.card_ord] using Ordinal.card_le_card (Ordinal.div_le_of_le_mul hhi)
  exact (ordinalSpaceInitialInfiniteSumEquiv (𝕜 := 𝕜) c hc α hlo hhi).trans
    ((CZeroSum.reindex (𝕜 := 𝕜)
      (E := fun _ : Set.Iio (α / c.ord) => ordinalEndpointZero 𝕜 c.ord)
      (Ordinal.enumIsoToType (α / c.ord)).symm.toEquiv).toContinuousLinearEquiv.trans
      ((singularEndpointSmallerReplication hc hs (α / c.ord) hγ hγc).symm.trans
        (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) c.ord hκ).symm))

end Posets
