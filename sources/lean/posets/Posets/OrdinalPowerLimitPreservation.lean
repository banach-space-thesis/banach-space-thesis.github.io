import Posets.OrdinalEndpointNearDiagonalPreservation
import JLMS.OrdinalSpacePowerLimit
import ThesisCommon.Analysis.PrimaryIsomorphism

/-! A controlled operator-preservation step on the actual higher limit
power C-space. The fixed block model is Kislyakov's genuine cofinal c₀
decomposition. The local factor bounds and small off-diagonal rows remain
explicit inputs; no assertion that they hold for every operator is made. -/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace Posets
open JLMS ThesisCommon
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

local instance powerPreservationFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance powerPreservationFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance
local instance powerPreservationEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerPreservationEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance powerPreservationSumGroup {I : Type*} (α : I → Ordinal.{u}) :
    NormedAddCommGroup (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance
local instance powerPreservationSumSpace {I : Type*} (α : I → Ordinal.{u}) :
    NormedSpace 𝕜 (CZeroSum 𝕜 (fun i => ordinalEndpointZero 𝕜 (α i))) := inferInstance

def ordinalPowerLimitBlockOrdinal (c : Cardinal.{u}) (γ : Ordinal.{u})
    (ξ : Set.Iio γ.cof.ord) : Ordinal.{u} :=
  c.ord ^ Order.succ (ordinalPowerBlockPredecessor γ ξ.val)

theorem ordinalPowerLimitBlockOrdinal_monotone (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) : Monotone (ordinalPowerLimitBlockOrdinal c γ) := by
  intro ξ η hξη
  apply Ordinal.opow_le_opow_right (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc))
  rw [← ordinalPowerBlockPredecessor_spec, ← ordinalPowerBlockPredecessor_spec]
  exact (ordinalCofinalExponent_isNormal γ).monotone (Order.succ_le_succ hξη)

def ordinalPowerLimitFactorModel (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) (hcard : γ.card ≤ c) :
    OrdinalC 𝕜 (c.ord ^ γ) ≃L[𝕜]
      CZeroSum 𝕜 (fun ξ => ordinalEndpointZero 𝕜 (ordinalPowerLimitBlockOrdinal c γ ξ)) :=
  (ordinalSpaceEndpointZeroEquiv (𝕜 := 𝕜) (c.ord ^ γ)
    (ordinalInitialPower_infinite c hc γ
      (Ordinal.one_lt_omega0.le.trans (Ordinal.omega0_le_of_isSuccLimit hγ)))).trans
    (ordinalEndpointZeroPowerLimitSum (𝕜 := 𝕜) c hc γ hγ hcard)

def ordinalPowerLimitOperatorBound (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) (hcard : γ.card ≤ c) (K : ℝ) : ℝ :=
  (4 * K) * (‖(ordinalPowerLimitFactorModel (𝕜 := 𝕜) c hc γ hγ hcard).toContinuousLinearMap‖ *
    ‖(ordinalPowerLimitFactorModel (𝕜 := 𝕜) c hc γ hγ hcard).symm.toContinuousLinearMap‖) ^ 2

theorem ordinalPowerLimit_nearDiagonal_dichotomy
    (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (γ : Ordinal.{u}) (hγ : Order.IsSuccLimit γ) (hcard : γ.card ≤ c)
    (T : OrdinalC 𝕜 (c.ord ^ γ) →L[𝕜] OrdinalC 𝕜 (c.ord ^ γ))
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsmall : (2 * K) * ε < 1 / 2) :
    let e := ordinalPowerLimitFactorModel (𝕜 := 𝕜) c hc γ hγ hcard
    let S := (e.toContinuousLinearMap.comp T).comp e.symm.toContinuousLinearMap
    (∀ i,
      FactorsIdentityWith (cZeroOperatorBlock S i i)
        (ordinalEndpointZero 𝕜 (ordinalPowerLimitBlockOrdinal c γ i)) K ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - cZeroOperatorBlock S i i)
        (ordinalEndpointZero 𝕜 (ordinalPowerLimitBlockOrdinal c γ i)) K) →
    (∀ i (s : Finset (Set.Iio γ.cof.ord)),
      ∑ j ∈ s.erase i, ‖cZeroOperatorBlock S i j‖ ≤ ε) →
    FactorsIdentityWith T (OrdinalC 𝕜 (c.ord ^ γ))
      (ordinalPowerLimitOperatorBound (𝕜 := 𝕜) c hc γ hγ hcard K) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T) (OrdinalC 𝕜 (c.ord ^ γ))
      (ordinalPowerLimitOperatorBound (𝕜 := 𝕜) c hc γ hγ hcard K) := by
  intro e S hlocal hrow
  have hbound : ((4 * K) * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)) *
      (‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖) =
      ordinalPowerLimitOperatorBound (𝕜 := 𝕜) c hc γ hγ hcard K := by
    change (4 * K) * (_ * _) * (_ * _) = (4 * K) * (_ * _) ^ 2
    ring
  rcases ordinalEndpointSum_nearDiagonal_dichotomy (Cardinal.isRegular_cof hγ)
    (ordinalPowerLimitBlockOrdinal c γ) (ordinalPowerLimitBlockOrdinal_monotone c hc γ)
    S hK hε hsmall hlocal hrow with h | h
  · left
    have hf := (h.of_compression e.toContinuousLinearMap e.symm.toContinuousLinearMap).target_equiv e.symm
    simpa only [ContinuousLinearEquiv.symm_symm, hbound] using hf
  · right
    have hcomp : (e.toContinuousLinearMap.comp
        (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 (c.ord ^ γ)) - T)).comp
        e.symm.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _ - S := by
      apply compression_complement T e.toContinuousLinearMap e.symm.toContinuousLinearMap
      apply ContinuousLinearMap.ext
      intro x
      exact e.apply_symm_apply x
    rw [← hcomp] at h
    have hf := (h.of_compression e.toContinuousLinearMap e.symm.toContinuousLinearMap).target_equiv e.symm
    simpa only [ContinuousLinearEquiv.symm_symm, hbound] using hf

end Posets
