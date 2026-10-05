import PFP.OrdinalFixedExponentNormalization
import JLMS.OrdinalSpaceSingularFullReplication
import JLMS.OrdinalSpaceSingularReplication
import JLMS.OrdinalSpaceInitialInfiniteReduction
import JLMS.OrdinalSpaceInitialFiniteReduction
import JLMS.OrdinalSpaceEndpointZeroBounded

/-! Actual singular initial-ordinal reductions, without a factorisation assumption.
The maps combine endpoint-zero replication, quotient blocks and finite products. -/
noncomputable section
namespace Posets.UniverseSingularInitial
open JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

local instance singularPolyEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance singularPolyEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
def singularEndpointSmallerReplication {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (γ : Ordinal.{u}) (hγ : Ordinal.omega0 ≤ γ) (hγc : γ.card ≤ c) :
    ordinalEndpointZero 𝕜 c.ord ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : γ.toType => ordinalEndpointZero 𝕜 c.ord) := by
  letI : Infinite c.ord.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hc)
  letI : Infinite γ.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Ordinal.card_omega0] using Ordinal.card_le_card hγ)
  let e := (ordinalEndpointZeroSingularInitialReplication (𝕜 := 𝕜) c hc hs).trans
    (CZeroSum.reindex (𝕜 := 𝕜) (E := fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 c.ord)
      (Ordinal.enumIsoToType c.ord).symm.toEquiv).toContinuousLinearEquiv
  exact Posets.UniverseFixedExponent.cZeroSum_smallerReplication
    (by simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hγc) e

def singularInitialInfiniteQuotientEquiv {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (α : Ordinal.{u}) (hlo : c.ord * Ordinal.omega0 ≤ α) (hhi : α ≤ c.ord * c.ord) :
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

def ordinalSingularFiniteMultipleEquiv {c : Cardinal.{u}} (hc : Cardinal.aleph0 ≤ c)
    (hs : ¬ c.IsRegular) (n : ℕ) :
    OrdinalC 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) ≃L[𝕜] OrdinalC 𝕜 c.ord := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hc
  exact (ordinalSpaceFinitePower (𝕜 := 𝕜) c.ord hκ n).trans
    (Posets.UniverseFixedExponent.finitePiCollapseEquiv (ordinalSpaceSingularInitialSquareEquiv (𝕜 := 𝕜) c hc hs) n)

def singularInitialBelowSquareEquiv {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (α : Ordinal.{u}) (hlo : c.ord ≤ α) (hhi : α ≤ c.ord * c.ord) :
    OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 c.ord := by
  refine Classical.choice ?_
  by_cases hω : α < c.ord * Ordinal.omega0
  · obtain ⟨n, ρ, hρ, hα⟩ := exists_initial_finite_quotient_remainder c hc α hlo hω
    have hmul : c.ord ≤ c.ord * ((n + 1 : ℕ) : Ordinal) := by
      calc
        c.ord = c.ord * 1 := (mul_one _).symm
        _ ≤ c.ord * ((n + 1 : ℕ) : Ordinal) :=
          mul_le_mul_left' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) _
    exact ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) hα).toContinuousLinearEquiv.trans
      ((ordinalSpaceSmallRemainder c hc _ ρ hmul hρ).trans
        (ordinalSingularFiniteMultipleEquiv hc hs n))⟩
  · exact ⟨singularInitialInfiniteQuotientEquiv hc hs α (le_of_not_gt hω) hhi⟩


end Posets.UniverseSingularInitial

