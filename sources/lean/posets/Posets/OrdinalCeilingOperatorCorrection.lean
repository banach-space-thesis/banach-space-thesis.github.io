import JLMS.OrdinalSpaceRetractionBounded

/-! Literal ceiling projections and corrected complementary operators. -/

noncomputable section
open Set Order
universe u
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000

variable (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β))
  (hg : StrictMono g)
  (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)

def ordinalCeilingProjection : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  (JLMS.ordinalSpaceCeilingExtension g hg htop).comp (JLMS.ordinalSpaceRestriction g)

@[simp] theorem ordinalCeilingProjection_apply (f : JLMS.OrdinalC 𝕜 β)
    (x : JLMS.OrdinalInterval β) :
    ordinalCeilingProjection g hg htop f x = f (g (JLMS.ordinalEmbeddingCeiling g x)) := rfl

theorem ordinalCeilingProjection_norm_le :
    ‖ordinalCeilingProjection (𝕜 := 𝕜) g hg htop‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  simpa using mul_le_mul (JLMS.norm_ordinalSpaceCeilingExtension_le g hg htop)
    (JLMS.norm_ordinalSpaceRestriction_le g) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

def ordinalCeilingComplement : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β :=
  ContinuousLinearMap.id 𝕜 _ - ordinalCeilingProjection g hg htop

theorem ordinalCeilingComplement_norm_le :
    ‖ordinalCeilingComplement (𝕜 := 𝕜) g hg htop‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by
    have := ordinalCeilingProjection_norm_le (𝕜 := 𝕜) g hg htop
    have := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := JLMS.OrdinalC 𝕜 β)
    linarith)

def ordinalCeilingCorrectedLeft (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :=
  (ordinalCeilingComplement g hg htop).comp T + ordinalCeilingProjection g hg htop

def ordinalCeilingCorrectedRight (S : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :=
  (ordinalCeilingComplement g hg htop).comp S

theorem ordinalCeiling_corrected_sum
    (T S : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _) :
    ordinalCeilingCorrectedLeft g hg htop T + ordinalCeilingCorrectedRight g hg htop S =
      ContinuousLinearMap.id 𝕜 _ := by
  unfold ordinalCeilingCorrectedLeft ordinalCeilingCorrectedRight
  rw [add_right_comm, ← ContinuousLinearMap.comp_add, hTS, ContinuousLinearMap.comp_id]
  exact sub_add_cancel _ _

theorem ordinalCeilingCorrectedLeft_norm_le
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    ‖ordinalCeilingCorrectedLeft g hg htop T‖ ≤ 2 * ‖T‖ + 1 := by
  apply (norm_add_le _ _).trans
  apply add_le_add _ (ordinalCeilingProjection_norm_le g hg htop)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (ordinalCeilingComplement_norm_le g hg htop) (norm_nonneg T))

theorem ordinalCeilingCorrectedRight_norm_le
    (S : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β) :
    ‖ordinalCeilingCorrectedRight g hg htop S‖ ≤ 2 * ‖S‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (ordinalCeilingComplement_norm_le g hg htop) (norm_nonneg S))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem ordinalCeilingProjection_comp_eq_zero
    (J : E →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (hJ : ∀ f x, J f (g x) = 0) :
    (ordinalCeilingProjection g hg htop).comp J = 0 := by
  ext f x
  exact hJ f (JLMS.ordinalEmbeddingCeiling g x)

theorem ordinalCeilingCorrectedLeft_comp_of_range_zero
    (T : JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.OrdinalC 𝕜 β)
    (J : E →L[𝕜] JLMS.OrdinalC 𝕜 β) (hJ : ∀ f x, J f (g x) = 0) :
    (ordinalCeilingCorrectedLeft g hg htop T).comp J =
      (ordinalCeilingComplement g hg htop).comp (T.comp J) := by
  rw [ordinalCeilingCorrectedLeft, ContinuousLinearMap.add_comp,
    ordinalCeilingProjection_comp_eq_zero g hg htop J hJ, add_zero, ContinuousLinearMap.comp_assoc]

end Posets
