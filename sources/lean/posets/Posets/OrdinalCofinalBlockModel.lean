import Posets.OrdinalCofinalBlockMaps
import JLMS.OrdinalSpacePowerLimit
import Posets.WolfeLaminarEmbeddingOrdinal

/-! A fixed countable block model for the ordinal space at a limit exponent. -/
noncomputable section
open Set Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def ordinalCofinalBlockIndex (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) : ℕ ≃ Iio γ.cof.ord := by
  letI : Infinite (Iio γ.cof.ord) := JLMS.ordinalIioInfinite _
    (JLMS.ordinalPowerLimit_cofinality_infinite γ hγ)
  letI : Countable (Iio γ.cof.ord) := Cardinal.mk_le_aleph0_iff.mp (by
    rw [Ordinal.mk_Iio_ordinal, Cardinal.card_ord]
    exact Cardinal.lift_le_aleph0.mpr ((Ordinal.cof_le_card γ).trans hc))
  exact Classical.choice nonempty_equiv_of_countable

def ordinalCofinalBlockExponent (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) (n : ℕ) : Ordinal.{0} :=
  succ (JLMS.ordinalPowerBlockPredecessor γ (ordinalCofinalBlockIndex γ hγ hc n).val)

theorem ordinalCofinalBlockExponent_lt (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) (n : ℕ) : ordinalCofinalBlockExponent γ hγ hc n < γ := by
  have h := JLMS.ordinalCofinalExponent_successor_lt γ hγ
    (ordinalCofinalBlockIndex γ hγ hc n).property
  rwa [JLMS.ordinalPowerBlockPredecessor_spec] at h

theorem ordinalCofinalBlockExponent_ne_zero (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) (n : ℕ) : ordinalCofinalBlockExponent γ hγ hc n ≠ 0 :=
  Ordinal.succ_ne_zero _

def ordinalCofinalBlockEquiv (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) :
    OrdinalContinuous 𝕜 (ω ^ γ) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun n : ℕ => JLMS.ordinalEndpointZero 𝕜
        (ω ^ ordinalCofinalBlockExponent γ hγ hc n)) := by
  have hinf : ω ≤ (ω : Ordinal.{0}) ^ γ := by
    simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (Ordinal.one_le_iff_ne_zero.mpr hγ.ne_bot)
  let e : JLMS.ordinalEndpointZero 𝕜 ((ω : Ordinal.{0}) ^ γ) ≃L[𝕜]
      JLMS.CZeroSum 𝕜 (fun ξ : Iio γ.cof.ord => JLMS.ordinalEndpointZero 𝕜
        (ω ^ succ (JLMS.ordinalPowerBlockPredecessor γ ξ.val))) := by
    have e := JLMS.ordinalEndpointZeroPowerLimitSum (𝕜 := 𝕜) Cardinal.aleph0 le_rfl γ hγ hc
    rw [Cardinal.ord_aleph0] at e
    exact e
  exact ((JLMS.ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) _ hinf).trans e).trans
    (JLMS.CZeroSum.reindex (𝕜 := 𝕜) (ordinalCofinalBlockIndex γ hγ hc)).toContinuousLinearEquiv

end Posets
