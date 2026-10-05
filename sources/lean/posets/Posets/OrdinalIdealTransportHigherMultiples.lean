import Posets.OrdinalIdealTransportRegularPowers
import Posets.OrdinalIdealTransportSingularReplication
import Posets.OrdinalIdealTransportLowRank
import JLMS.OrdinalSpaceMultipleSquare

/-! Smaller positive ordinal multiples of a finite higher power have the
same continuous-function space as the initial square. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance higherMultipleEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance higherMultipleEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance

def initialOrdinalSquareSquareEquiv {c : Cardinal.{0}} (hu : Cardinal.aleph0 < c) :
    OrdinalC 𝕜 (c.ord * c.ord) ≃L[𝕜]
      OrdinalC 𝕜 (c.ord * c.ord) × OrdinalC 𝕜 (c.ord * c.ord) := by
  letI : Infinite c.ord.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hu.le)
  let e := initialOrdinalSquareSumEquiv (𝕜 := 𝕜) hu
  exact e.trans ((JLMS.CZeroSum.infiniteSquareIsometry (𝕜 := 𝕜) c.ord.toType
    (OrdinalC 𝕜 c.ord)).toContinuousLinearEquiv.trans (e.symm.prodCongr e.symm))

def initialSquareEndpointSmallerReplication {c : Cardinal.{0}}
    (hc : Cardinal.aleph0 ≤ c) (η : Ordinal.{0}) (hη : Ordinal.omega0 ≤ η) (hηc : η.card ≤ c) :
    ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal)) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun _ : η.toType => ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal))) := by
  letI : Infinite c.ord.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hc)
  letI : Infinite η.toType := Cardinal.infinite_iff.mpr (by
    simpa only [Cardinal.mk_toType, Ordinal.card_omega0] using Ordinal.card_le_card hη)
  have r := ordinalEndpointZeroPowerSuccessorReplication (𝕜 := 𝕜) c hc 1 le_rfl
  rw [Ordinal.succ_one] at r
  let e := r.trans (JLMS.CZeroSum.reindex (𝕜 := 𝕜)
    (E := fun _ : Set.Iio c.ord => ordinalEndpointZero 𝕜 (c.ord ^ (2 : Ordinal)))
    (Ordinal.enumIsoToType c.ord).symm.toEquiv).toContinuousLinearEquiv
  exact cZeroSum_smallerReplication
    (by simpa only [Cardinal.mk_toType, Cardinal.card_ord] using hηc) e

def initialHigherFinitePowerMultipleEquiv {c : Cardinal.{0}}
    (hu : Cardinal.aleph0 < c) (n : ℕ) (η : Ordinal.{0}) (hη : 0 < η) (hηκ : η < c.ord) :
    OrdinalC 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal) * η) ≃L[𝕜]
      OrdinalC 𝕜 (c.ord * c.ord) := by
  refine Classical.choice ?_
  have hn : (1 : Ordinal.{0}) ≤ ((n+2 : ℕ) : Ordinal) := by exact_mod_cast (show 1 ≤ n+2 by omega)
  have hinf := ordinalInitialPower_infinite c hu.le ((n+2 : ℕ) : Ordinal) hn
  by_cases hηω : η < Ordinal.omega0
  · obtain ⟨m, rfl⟩ := exists_nat_succ_of_positive_finite_ordinal hη hηω
    exact ⟨(ordinalSpaceFinitePower (𝕜 := 𝕜) _ hinf m).trans
      ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin (m+1) => initialHigherFinitePowerEquiv hu.le n)).trans
        (finitePiCollapseEquiv (initialOrdinalSquareSquareEquiv hu) m))⟩
  · have hηω' := le_of_not_gt hηω
    have hbase : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    have hκ : c.ord ≤ c.ord ^ ((n+2 : ℕ) : Ordinal) := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
        (Ordinal.omega0_pos.trans_le hbase) hn
    have habs : η + c.ord ^ ((n+2 : ℕ) : Ordinal) = c.ord ^ ((n+2 : ℕ) : Ordinal) :=
      small_add_eq_of_initial_le c hu.le _ η hκ hηκ
    let d := (ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
      (hinf.trans (Ordinal.le_mul_left _ hη))).trans
        (ordinalEndpointZeroMultipleSumEquiv (𝕜 := 𝕜) _ η hinf hηω' (Or.inr habs))
    let e := initialHigherFinitePowerEndpointEquiv (𝕜 := 𝕜) hu.le n
    let r := initialSquareEndpointSmallerReplication (𝕜 := 𝕜) hu.le η hηω'
      (Cardinal.lt_ord.mp hηκ).le
    have hpow : c.ord ^ (2 : Ordinal) = c.ord * c.ord := by
      rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
    exact ⟨d.trans
      ((JLMS.CZeroSum.reindex (𝕜 := 𝕜)
        (E := fun _ : Set.Iio η => ordinalEndpointZero 𝕜 (c.ord ^ ((n+2 : ℕ) : Ordinal)))
        (Ordinal.enumIsoToType η).symm.toEquiv).toContinuousLinearEquiv.trans
        ((JLMS.CZeroSum.congrRight (fun _ : η.toType => e)
          (norm_nonneg _) (norm_nonneg _) (fun _ => le_rfl) (fun _ => le_rfl)).trans
          (r.symm.trans ((ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
            (ordinalInitialPower_infinite c hu.le 2 one_le_two)).symm.trans
              (ordinalSpaceCongrIsometry (𝕜 := 𝕜) hpow).toContinuousLinearEquiv))))⟩

end Posets
