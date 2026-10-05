import JLMS.OgdenCommonProjections
import JLMS.ContinuityIdealGeneration

/-!
# Ogden Propositions 6.16 and the ideal-containment step of 6.18

A constant family in the common-projection theorem puts M₀ in the continuity
ideal. In particular, every operator whose endpoint column vanishes belongs
to that ideal (Proposition 6.16). Two concrete rank-one operators give the
missing scalar direction and yield M ⊆ J, as in the proof of Theorem 6.18.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance] ordinalLimitFunctionGroup ordinalLimitFunctionSpace
  ordinalLimitOperatorGroup ordinalLimitOperatorSpace ordinalLimitOperatorAlgebra
  ordinalLimitOperatorScalarTower ordinalLimitOperatorScalarComm

theorem loyWillisZeroEndpointSubspace_le_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A) :
    loyWillisZeroEndpointSubspace hc hu ≤ continuityIdeal (𝕜 := 𝕜)
      (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ := by
  intro T hT
  obtain ⟨a, ha, b, hb, hfactor⟩ :=
    exists_ogden_common_ideal_factors hc hu θ (fun _ : ℕ => T) (fun _ => hT)
  rw [hfactor 0]
  exact (continuityIdeal θ).add_mem
    (continuityIdeal_mul_right θ (T - T * b) ha) (continuityIdeal_mul_left θ T hb)

theorem mem_loyWillisZeroEndpointSubspace_of_zero_column
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : ∀ x : OrdinalInterval c.ord,
      ordinalOperatorMatrix c.ord T x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) :
    T ∈ loyWillisZeroEndpointSubspace hc hu := by
  refine ⟨?_, hT _⟩
  apply mem_loyWillisSubspace_of_continuous_endpointColumn hc hu
  have he : (fun x => ordinalOperatorMatrix c.ord T x
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) = fun _ : OrdinalInterval c.ord => (0 : 𝕜) :=
    funext hT
  rw [he]
  exact continuous_const

/-- Ogden Proposition 6.16. -/
theorem ogden_zero_endpoint_column_mem_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : ∀ x : OrdinalInterval c.ord,
      ordinalOperatorMatrix c.ord T x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0) :
    T ∈ continuityIdeal (𝕜 := 𝕜)
      (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ :=
  loyWillisZeroEndpointSubspace_le_continuityIdeal hc hu θ
    (mem_loyWillisZeroEndpointSubspace_of_zero_column hc hu T hT)

/-- The algebraic containment M ⊆ J in Ogden Theorem 6.18. -/
theorem loyWillisSubspace_le_continuityIdeal
    {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (θ : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₙₐ[𝕜] A) :
    loyWillisSubspace hc hu ≤ continuityIdeal (𝕜 := 𝕜)
      (B := OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (A := A) θ := by
  let z : OrdinalInterval c.ord := ⟨0, le_rfl, Ordinal.zero_le _⟩
  let e : OrdinalInterval c.ord := ⟨c.ord, Ordinal.zero_le _, le_rfl⟩
  let f : OrdinalC 𝕜 c.ord := ordinalHeadIndicator c.ord 0
  let a : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord :=
    (ContinuousMap.evalCLM (R := 𝕜) z).smulRight (ContinuousMap.const _ 1)
  let b : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord := ordinalEndpointRankOne c.ord f
  have hez : e ≠ z := by
    intro he
    have hκ := congrArg Subtype.val he
    exact (ne_of_gt (Cardinal.isSuccLimit_ord hu.le).bot_lt) hκ
  have hcol (x : OrdinalInterval c.ord) : ordinalOperatorMatrix c.ord a x e = 0 := by
    change ordinalOperatorMatrix c.ord
      ((ContinuousMap.evalCLM (R := 𝕜) z).smulRight (ContinuousMap.const _ 1)) x e = 0
    rw [ordinalOperatorMatrix_rankOne, if_neg hez]
  have ha : a ∈ loyWillisZeroEndpointSubspace hc hu :=
    mem_loyWillisZeroEndpointSubspace_of_zero_column hc hu a hcol
  have hb : b ∈ loyWillisSubspace hc hu := ordinalEndpointRankOne_mem_loyWillisSubspace hc hu f
  have hab : a * b = ordinalEndpointRankOne c.ord (ContinuousMap.const _ 1) := by
    ext w x
    change (w e * f z) * 1 = w e * 1
    simp [f, z]
  apply continuityIdeal_contains_of_kernel_and_product θ (loyWillisSubspace hc hu)
    (ordinalEndpointCoefficient c.ord).toLinearMap
    (fun a _ b hb => loyWillisSubspace_mul_left hc hu a b hb)
    (fun T hT hzero => loyWillisZeroEndpointSubspace_le_continuityIdeal hc hu θ ⟨hT, hzero⟩)
    a b ha.1 hb ha.2
  rw [hab]
  change ordinalOperatorMatrix c.ord (ordinalEndpointRankOne c.ord (ContinuousMap.const _ 1)) e e ≠ 0
  rw [ordinalOperatorMatrix_endpointRankOne]
  exact one_ne_zero

end JLMS
