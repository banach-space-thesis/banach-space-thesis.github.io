import Posets.OrdinalIdealTransportRegularTail

/-! The scalar endpoint jump can be extracted beyond any prescribed cutoff.
The same bounded maps annihilate every sufficiently small off-diagonal block. -/
noncomputable section
namespace Posets
open JLMS
variable {𝕜 : Type} [RCLike 𝕜]
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
  JLMS.ordinalLimitOperatorGroup JLMS.ordinalLimitOperatorSpace JLMS.ordinalLimitOperatorAlgebra
  JLMS.ordinalLimitOperatorScalarTower JLMS.ordinalLimitOperatorScalarComm
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

theorem exists_initialOrdinal_scalar_tail_compression
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (δ : Ordinal.{0}) (hδ : δ < c.ord) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧
      L.comp (T.comp R) = initialEndpointJump (𝕜 := 𝕜) hc hu T •
        ContinuousLinearMap.id 𝕜 _ ∧
      (∀ f, R f ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      (∀ f x, x.val ≤ δ → R f x = 0) ∧
      (∀ f ∈ ordinalTailSpace c.ord δ, L f = 0) := by
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
  obtain ⟨L, R, hLR, hLSR, hRtop, hL, hR, hhead, htail⟩ :=
    exists_loyWillis_zeroEndpoint_bounded_tail_compression hc hu S hS δ hδ
  refine ⟨L, R, hLR, ?_, hRtop, hL, hR, hhead, htail⟩
  apply ContinuousLinearMap.ext
  intro x
  have hSR : S (R x) = T (R x) - a • R x := by
    ext y
    change (T (R x) y - a * R x y) -
      R x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ * f y = _
    rw [hRtop, zero_mul, sub_zero]
    rfl
  have hz := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLSR
  have hid := congrArg (fun V : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord => V x) hLR
  change L (R x) = x at hid
  change L (S (R x)) = 0 at hz
  rw [hSR, map_sub, map_smul, hid] at hz
  exact sub_eq_zero.mp hz

theorem exists_initialOrdinal_scalar_compression_small_family
    {c : Cardinal.{0}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    {σ : Ordinal.{0}} (hσ : σ.card < c)
    (α : ∀ ξ < σ, Ordinal.{0}) (hα : ∀ ξ hξ, (α ξ hξ).card < c)
    (U : ∀ ξ hξ, OrdinalC 𝕜 (α ξ hξ) →L[𝕜] OrdinalC 𝕜 c.ord)
    (V : ∀ ξ hξ, OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 (α ξ hξ)) :
    ∃ L R : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord,
      L.comp R = ContinuousLinearMap.id 𝕜 _ ∧
      L.comp (T.comp R) = initialEndpointJump (𝕜 := 𝕜) hc hu T •
        ContinuousLinearMap.id 𝕜 _ ∧ ‖L‖ ≤ 4 ∧ ‖R‖ ≤ 2 ∧
      (∀ ξ hξ, L.comp (U ξ hξ) = 0) ∧
      (∀ ξ hξ, (V ξ hξ).comp R = 0) := by
  have hcof : c.ord.cof = c := hc.cof_eq
  have hκ : Cardinal.aleph0 < c.ord.cof := by simpa only [hcof] using hu
  have ha (ξ) (hξ : ξ < σ) : (α ξ hξ).card < c.ord.cof := by
    simpa only [hcof] using hα ξ hξ
  have hu' (ξ) (hξ : ξ < σ) := exists_smallDomain_operator_tail hκ (ha ξ hξ) (U ξ hξ)
  have hv' (ξ) (hξ : ξ < σ) :=
    exists_smallCodomain_operator_annihilating_tail hκ (ha ξ hξ) (V ξ hξ)
  choose b hb hU using hu'
  choose d hd hV using hv'
  let δ := Ordinal.bsup σ (fun ξ hξ => max (b ξ hξ) (d ξ hξ))
  have hδ : δ < c.ord := Ordinal.bsup_lt_ord (by simpa only [hcof] using hσ)
    (fun ξ hξ => max_lt (hb ξ hξ) (hd ξ hξ))
  obtain ⟨L, R, hLR, hLTR, htop, hL, hR, hhead, htail⟩ :=
    exists_initialOrdinal_scalar_tail_compression hc hu T δ hδ
  refine ⟨L, R, hLR, hLTR, hL, hR, ?_, ?_⟩
  · intro ξ hξ
    apply ContinuousLinearMap.ext
    intro f
    apply htail
    intro x hx
    exact hU ξ hξ f x (((le_max_left _ _).trans
      (Ordinal.le_bsup _ ξ hξ)).trans_lt hx)
  · intro ξ hξ
    apply ContinuousLinearMap.ext
    intro f
    apply hV ξ hξ _ (fun x hx => hhead f x (hx.trans
      ((le_max_right _ _).trans (Ordinal.le_bsup _ ξ hξ)))) (htop f)

end Posets
