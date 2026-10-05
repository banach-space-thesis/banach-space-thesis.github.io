/- Universe-polymorphic extension of Posets.OrdinalIdealTransportSmallFamilyScalars. Actual maps and bounds retained; paper-specific ideal statements omitted where they are not needed. -/
import LPCK.GenericOrdinalSmallFamilyCompression

/-! One common bounded compression extracts all endpoint jumps in a
cardinally small family. In particular it applies to every entry of a cardinally small
operator block matrix. -/
noncomputable section
universe u
namespace LPCK.GenericOrdinal
set_option synthInstance.maxHeartbeats 200000
open JLMS
variable {𝕜 : Type} [RCLike 𝕜] {I : Type u} [Nonempty I]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 800000

theorem exists_initialOrdinal_scalar_smallFamily_compression
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧
      ∀ n, L.comp ((T n).comp R) = initialEndpointJump (𝕜 := 𝕜) hc hu (T n) •
        ContinuousLinearMap.id 𝕜 _ := by
  let a (n : I) : 𝕜 := initialEndpointJump (𝕜 := 𝕜) hc hu (T n)
  let U (n : I) := T n - a n • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)
  have hU (n) : U n ∈ loyWillisSubspace hc hu := sub_jump_smul_id_mem_loyWillisSubspace hc hu (T n)
  let f (n : I) := loyWillisEndpointColumn hc hu (U n) (hU n)
  let S (n : I) := U n - ordinalEndpointRankOne c.ord (f n)
  have hS (n) : S n ∈ loyWillisZeroEndpointSubspace hc hu := by
    refine ⟨loyWillis_sub_endpointRankOne_mem hc hu (U n) (hU n), ?_⟩
    change ordinalOperatorMatrix c.ord (S n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0
    exact loyWillis_sub_endpointRankOne_zero_column hc hu (U n) (hU n) _
  obtain ⟨L, R, hLR, hLSR, hRtop, hL, hR⟩ :=
    exists_loyWillis_zeroEndpoint_bounded_smallFamily_compression hc hu hI S hS
  refine ⟨L, R, hLR, hL, hR, hRtop, ?_⟩
  intro n
  apply ContinuousLinearMap.ext
  intro x
  have hSR : S n (R x) = T n (R x) - a n • R x := by
    ext y
    change (T n (R x) y - a n * R x y) -
      R x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ * f n y = _
    rw [hRtop, zero_mul, sub_zero]
    rfl
  have hz := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) (hLSR n)
  have hid := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLR
  change L (R x) = x at hid
  change L (S n (R x)) = 0 at hz
  rw [hSR, map_sub, map_smul, hid] at hz
  exact sub_eq_zero.mp hz


end LPCK.GenericOrdinal




