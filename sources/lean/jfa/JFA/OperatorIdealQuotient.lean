import JFA.Definitions
import Mathlib.Analysis.Normed.Operator.Banach

/-! The closed two-sided ideal correspondence for a surjective bounded linear
map between operator algebras that preserves composition. Ideals above the
actual kernel correspond by image and preimage. The Banach open mapping theorem
proves closedness of their images; closedness is not an extra hypothesis. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

local instance : NormedAddCommGroup (E →L[𝕜] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (E →L[𝕜] E) := ContinuousLinearMap.toNormedSpace
local instance : ContinuousAdd (E →L[𝕜] E) :=
  (ContinuousLinearMap.topologicalAddGroup : IsTopologicalAddGroup (E →L[𝕜] E)).toContinuousAdd
local instance : NormedAddCommGroup (F →L[𝕜] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace 𝕜 (F →L[𝕜] F) := ContinuousLinearMap.toNormedSpace
local instance : ContinuousAdd (F →L[𝕜] F) :=
  (ContinuousLinearMap.topologicalAddGroup : IsTopologicalAddGroup (F →L[𝕜] F)).toContinuousAdd

variable (Φ : (E →L[𝕜] E) →L[𝕜] (F →L[𝕜] F))
variable (hcomp : ∀ A T : E →L[𝕜] E, Φ (A.comp T) = (Φ A).comp (Φ T))
variable (hsurj : Function.Surjective Φ)

omit [CompleteSpace E] [CompleteSpace F] in
include hcomp in
theorem closedOperatorIdeal_preimage {J : Set (F →L[𝕜] F)}
    (hJ : IsClosedOperatorIdeal 𝕜 F J) : IsClosedOperatorIdeal 𝕜 E (Φ ⁻¹' J) := by
  rcases hJ with ⟨hc, h0, ha, hs, hm⟩
  refine ⟨hc.preimage Φ.continuous, ?_, ?_, ?_, ?_⟩
  · change Φ 0 ∈ J
    simpa only [map_zero] using h0
  · intro T hT Q hQ
    change Φ (T + Q) ∈ J
    rw [map_add]
    exact ha _ hT _ hQ
  · intro a T hT
    change Φ (a • T) ∈ J
    rw [map_smul]
    exact hs _ _ hT
  · intro A T hT
    change Φ (A.comp T) ∈ J ∧ Φ (T.comp A) ∈ J
    rw [hcomp, hcomp]
    exact hm _ _ hT

omit [CompleteSpace E] [CompleteSpace F] in
theorem closedOperatorIdeal_preimage_image {I : Set (E →L[𝕜] E)}
    (hI : IsClosedOperatorIdeal 𝕜 E I) (hker : {T | Φ T = 0} ⊆ I) :
    Φ ⁻¹' (Φ '' I) = I := by
  rcases hI with ⟨_, _, ha, hs, _⟩
  ext T
  constructor
  · rintro ⟨Q, hQ, heq⟩
    have hdiff : T - Q ∈ I := hker (by
      change Φ (T - Q) = 0
      rw [map_sub, heq, sub_self])
    have hsum := ha Q hQ (T - Q) hdiff
    simpa only [add_sub_cancel] using hsum
  · intro hT
    exact ⟨T, hT, rfl⟩

include hcomp hsurj in
theorem closedOperatorIdeal_image {I : Set (E →L[𝕜] E)}
    (hI : IsClosedOperatorIdeal 𝕜 E I) (hker : {T | Φ T = 0} ⊆ I) :
    IsClosedOperatorIdeal 𝕜 F (Φ '' I) := by
  rcases hI with ⟨hc, h0, ha, hs, hm⟩
  have hclosed : IsClosed (Φ '' I) := (Φ.isQuotientMap hsurj).isClosed_preimage.mp (by
    rw [closedOperatorIdeal_preimage_image Φ ⟨hc, h0, ha, hs, hm⟩ hker]
    exact hc)
  refine ⟨hclosed, ⟨0, h0, map_zero Φ⟩, ?_, ?_, ?_⟩
  · rintro T ⟨A, hA, rfl⟩ Q ⟨B, hB, rfl⟩
    exact ⟨A + B, ha _ hA _ hB, map_add Φ A B⟩
  · rintro a T ⟨A, hA, rfl⟩
    exact ⟨a • A, hs _ _ hA, map_smul Φ a A⟩
  · rintro T Q ⟨B, hB, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj T
    exact ⟨⟨A.comp B, (hm A B hB).1, hcomp A B⟩,
      ⟨B.comp A, (hm A B hB).2, hcomp B A⟩⟩

omit [CompleteSpace E] [CompleteSpace F] in
theorem closedOperatorIdeal_kernel_subset_preimage {J : Set (F →L[𝕜] F)}
    (hJ : IsClosedOperatorIdeal 𝕜 F J) : {T | Φ T = 0} ⊆ Φ ⁻¹' J := by
  intro T hT
  change Φ T ∈ J
  rw [hT]
  exact hJ.2.1

/-- An order isomorphism of the actual closed two-sided ideal sets. -/
def closedOperatorIdealQuotientOrderIso :
    {I : Set (E →L[𝕜] E) | IsClosedOperatorIdeal 𝕜 E I ∧ {T | Φ T = 0} ⊆ I} ≃o
      {J : Set (F →L[𝕜] F) | IsClosedOperatorIdeal 𝕜 F J} where
  toFun I := ⟨Φ '' I.val, closedOperatorIdeal_image Φ hcomp hsurj I.property.1 I.property.2⟩
  invFun J := ⟨Φ ⁻¹' J.val, closedOperatorIdeal_preimage Φ hcomp J.property,
    closedOperatorIdeal_kernel_subset_preimage Φ J.property⟩
  left_inv I := Subtype.ext (closedOperatorIdeal_preimage_image Φ I.property.1 I.property.2)
  right_inv J := Subtype.ext (image_preimage_eq _ hsurj)
  map_rel_iff' := by
    intro I J
    change Φ '' I.val ⊆ Φ '' J.val ↔ I.val ⊆ J.val
    constructor
    · intro h T hT
      have hp : T ∈ Φ ⁻¹' (Φ '' J.val) := h (mem_image_of_mem Φ hT)
      rwa [closedOperatorIdeal_preimage_image Φ J.property.1 J.property.2] at hp
    · intro h
      exact image_mono h

end JFA
