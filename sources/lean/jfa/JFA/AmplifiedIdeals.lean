import JFA.AmplifiedQuotient
import JFA.OperatorIdealQuotient
import JFA.SeparableIdeal

/-! The closed-ideal correspondence in Theorem 1.6 on the actual amplified
space. The source ideals are exactly those containing the actual separable-range
ideal. Image and preimage preserve the full two-sided, norm-closed conditions. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

@[simp] theorem amplifiedScalarQuotient_kernel (h𝒜 : IsAlmostDisjoint 𝒜)
    (hc : HasContinuumSize 𝒜) (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    {T | amplifiedScalarQuotient h𝒜 hc hfew T = 0} =
      separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) := by
  ext T
  exact amplifiedScalarOperator_eq_zero_iff h𝒜 hc hfew T

def amplifiedClosedIdealOrderIso (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    {I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) |
      IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I ∧
        separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I} ≃o
      {J : Set (cZero 𝕜 →L[𝕜] cZero 𝕜) | IsClosedOperatorIdeal 𝕜 (cZero 𝕜) J} := by
  let Φ := amplifiedScalarQuotient (𝕜 := 𝕜) h𝒜 hc hfew
  have hcomp : ∀ A T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
      Φ (A.comp T) = (Φ A).comp (Φ T) := by
    intro A T
    exact amplifiedScalarOperator_comp h𝒜 hc hfew T A
  have hk : {T | Φ T = 0} = separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) :=
    amplifiedScalarQuotient_kernel h𝒜 hc hfew
  have hsurj := amplifiedScalarQuotient_surjective h𝒜 hc hfew
  refine {
    toFun := fun I => ⟨Φ '' I.val, closedOperatorIdeal_image Φ hcomp hsurj I.property.1
      (by rw [hk]; exact I.property.2)⟩
    invFun := fun J => ⟨Φ ⁻¹' J.val, closedOperatorIdeal_preimage Φ hcomp J.property,
      (by rw [← hk]; exact closedOperatorIdeal_kernel_subset_preimage Φ J.property)⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro I
    apply Subtype.ext
    exact closedOperatorIdeal_preimage_image Φ I.property.1 (by rw [hk]; exact I.property.2)
  · intro J
    exact Subtype.ext (image_preimage_eq _ hsurj)
  · intro I J
    change Φ '' I.val ⊆ Φ '' J.val ↔ I.val ⊆ J.val
    constructor
    · intro h T hT
      have hp : T ∈ Φ ⁻¹' (Φ '' J.val) := h (mem_image_of_mem Φ hT)
      rwa [closedOperatorIdeal_preimage_image Φ J.property.1 (by rw [hk]; exact J.property.2)] at hp
    · exact image_mono

theorem amplifiedClosedIdealOrderIso_image (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (I : {I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) |
      IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I ∧
        separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I}) :
    (amplifiedClosedIdealOrderIso h𝒜 hc hfew I).val =
      amplifiedScalarQuotient h𝒜 hc hfew '' I.val := by
  rfl

theorem amplifiedClosedIdealOrderIso_preimage (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (J : {J : Set (cZero 𝕜 →L[𝕜] cZero 𝕜) | IsClosedOperatorIdeal 𝕜 (cZero 𝕜) J}) :
    ((amplifiedClosedIdealOrderIso h𝒜 hc hfew).symm J).val =
      amplifiedScalarQuotient h𝒜 hc hfew ⁻¹' J.val := by
  rfl

end JFA
