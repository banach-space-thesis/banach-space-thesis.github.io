import Posets.OrdinalIdealTransportRegularCompression
import Posets.OrdinalIdealTransportOmega

/-! Primary factorisation for regular uncountable ordinal C-spaces, proved
from the actual matrix-cut compressions and the Loy–Willis endpoint jump. -/
noncomputable section
namespace Posets
open JLMS ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem initialOrdinal_factorsIdentity_of_jump_ne_zero
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hjump : initialEndpointJump (𝕜 := 𝕜) hc hu T ≠ 0) :
    ∃ A B : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      B.comp (T.comp A) = ContinuousLinearMap.id 𝕜 _ := by
  let a : 𝕜 := initialEndpointJump (𝕜 := 𝕜) hc hu T
  let U := T - a • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)
  have hU : U ∈ loyWillisSubspace hc hu := sub_jump_smul_id_mem_loyWillisSubspace hc hu T
  let f := loyWillisEndpointColumn hc hu U hU
  let S := U - ordinalEndpointRankOne c.ord f
  have hS : S ∈ loyWillisZeroEndpointSubspace hc hu := by
    refine ⟨loyWillis_sub_endpointRankOne_mem hc hu U hU, ?_⟩
    change ordinalOperatorMatrix c.ord S ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
    exact loyWillis_sub_endpointRankOne_zero_column hc hu U hU _
  obtain ⟨L, R, hLR, hLSR, hRtop⟩ := exists_loyWillis_zeroEndpoint_compression hc hu S hS
  have hSR (x : OrdinalC 𝕜 c.ord) : S (R x) = T (R x) - a • R x := by
    ext y
    change (T (R x) y - a * R x y) - R x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ * f y = _
    rw [hRtop, zero_mul, sub_zero]
    rfl
  have hcompression (x : OrdinalC 𝕜 c.ord) : L (T (R x)) = a • x := by
    have hz := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLSR
    have hid := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLR
    change L (R x) = x at hid
    change L (S (R x)) = 0 at hz
    rw [hSR, map_sub, map_smul, hid] at hz
    exact sub_eq_zero.mp hz
  refine ⟨R, a⁻¹ • L, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change a⁻¹ • L (T (R x)) = x
  rw [hcompression, smul_smul, inv_mul_cancel₀ hjump, one_smul]

theorem initialOrdinal_hasPFP {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) : HasPFP 𝕜 (OrdinalSpace 𝕜 c.ord) := by
  intro T
  by_cases hT : initialEndpointJump (𝕜 := 𝕜) hc hu T = 0
  · right
    have h : initialEndpointJump (𝕜 := 𝕜) hc hu (ContinuousLinearMap.id 𝕜 _ - T) ≠ 0 := by
      rw [map_sub, initialEndpointJump_id, hT, sub_zero]
      exact one_ne_zero
    obtain ⟨A, B, hAB⟩ := initialOrdinal_factorsIdentity_of_jump_ne_zero hc hu _ h
    exact ⟨B, A, by simpa only [ContinuousLinearMap.comp_assoc] using hAB⟩
  · left
    obtain ⟨A, B, hAB⟩ := initialOrdinal_factorsIdentity_of_jump_ne_zero hc hu T hT
    exact ⟨B, A, by simpa only [ContinuousLinearMap.comp_assoc] using hAB⟩

theorem proposition_3_1_regular {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) : Proposition_3_1 𝕜 c.ord := by
  intro _
  letI : Nonempty (Set.Icc (0 : Ordinal.{0}) c.ord) := ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  have h := uniqueMaximal_of_hasPFP (initialOrdinal_hasPFP (𝕜 := 𝕜) hc hu)
  exact ⟨h.2, fun _ => h.1⟩

theorem uniqueMaximalClosed_regular_finiteMultiple {c : Cardinal.{0}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) :
    HasUniqueMaximalClosedIdeal 𝕜
      (OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal)) →L[𝕜]
        OrdinalSpace 𝕜 (c.ord * ((n+1 : ℕ) : Ordinal))) := by
  have hκ : Ordinal.omega0 ≤ c.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
  exact (uniqueMaximalClosed_ordinal_finiteMultiple_iff c.ord hκ n).mpr
    ((proposition_3_1_regular hc hu hκ).1)

end Posets



