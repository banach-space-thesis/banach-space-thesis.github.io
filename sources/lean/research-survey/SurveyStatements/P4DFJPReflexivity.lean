import SurveyStatements.P4DFJPDualDensity

/-! Reflexivity of the actual square-summable DFJP gauge space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048

open Set Metric
open scoped ENNReal

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

lemma norm_banachAdjoint_le {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (T : A →L[𝕜] B) :
    ‖banachAdjoint T‖ ≤ ‖T‖ := by
  apply (banachAdjoint T).opNorm_le_bound (norm_nonneg _)
  intro φ
  change ‖φ.comp T‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le φ T).trans_eq (mul_comm _ _)

lemma norm_bidualMap_apply_le {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (T : A →L[𝕜] B)
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 A)) :
    ‖bidualMap T ξ‖ ≤ ‖T‖ * ‖ξ‖ := by
  apply (bidualMap T ξ).opNorm_le_bound (by positivity)
  intro φ
  change ‖ξ (banachAdjoint T φ)‖ ≤ _
  calc
    ‖ξ (banachAdjoint T φ)‖ ≤ ‖ξ‖ * ‖banachAdjoint T φ‖ := ξ.le_opNorm _
    _ ≤ ‖ξ‖ * (‖T‖ * ‖φ‖) := mul_le_mul_of_nonneg_left
      (((banachAdjoint T).le_opNorm φ).trans
        (mul_le_mul_of_nonneg_right (norm_banachAdjoint_le T) (norm_nonneg φ)))
      (norm_nonneg ξ)
    _ = (‖T‖ * ‖ξ‖) * ‖φ‖ := by ring

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E)

def finiteLift (s : Finset ℤ) : E →L[𝕜] DFJPSum D :=
  ∑ j ∈ s, (lp.singleContinuousLinearMap 𝕜 (DFJPScale D) 2 j).comp
    (DFJPScale.continuousLinearEquiv D j).symm.toContinuousLinearMap

lemma finiteLift_comp_inclusion (s : Finset ℤ) :
    (finiteLift D s).comp (inclusion D) =
      (lp2Projection (𝕜 := 𝕜) s).comp (dfjpDiagonal D).subtypeL := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, finiteLift, lp2Projection,
    ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change (DFJPScale.continuousLinearEquiv D j).symm (inclusion D f) = f.val j
  rw [← coordinate_eq D f j]
  exact (DFJPScale.continuousLinearEquiv D j).symm_apply_apply (f.val j)

lemma norm_finiteLift_sq (s : Finset ℤ) (x : E) :
    ‖finiteLift D s x‖ ^ 2 = ∑ j ∈ s, (dfjpGauge D.carrier j x) ^ 2 := by
  have h := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fun j => (DFJPScale.continuousLinearEquiv D j).symm x) s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  simpa only [finiteLift, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, DFJPScale.norm_eq_gauge] using h

lemma summable_gauge_sq_of_bidual_image (ξ : StrongDual 𝕜 (StrongDual 𝕜 (DFJPSpace D)))
    (x : E) (hx : NormedSpace.inclusionInDoubleDual 𝕜 E x = bidualMap (inclusion D) ξ) :
    Summable (fun j : ℤ => (dfjpGauge D.carrier j x) ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _)
  intro s
  rw [← norm_finiteLift_sq]
  have hT : ‖(lp2Projection (𝕜 := 𝕜) s).comp (dfjpDiagonal D).subtypeL‖ ≤ 1 := by
    apply ((lp2Projection (𝕜 := 𝕜) s).comp (dfjpDiagonal D).subtypeL).opNorm_le_bound (by norm_num)
    intro f
    simpa using norm_lp2Projection_apply_le (𝕜 := 𝕜) s f.val
  have hmap : bidualMap ((lp2Projection (𝕜 := 𝕜) s).comp (dfjpDiagonal D).subtypeL) ξ =
      NormedSpace.inclusionInDoubleDual 𝕜 (DFJPSum D) (finiteLift D s x) := by
    rw [← finiteLift_comp_inclusion, bidualMap_comp]
    change bidualMap (finiteLift D s) (bidualMap (inclusion D) ξ) = _
    rw [← hx, bidualMap_inclusion]
  have hn : ‖finiteLift D s x‖ ≤ ‖ξ‖ := by
    have hb := norm_bidualMap_apply_le
      ((lp2Projection (𝕜 := 𝕜) s).comp (dfjpDiagonal D).subtypeL) ξ
    rw [hmap] at hb
    change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (finiteLift D s x)‖ ≤ _ at hb
    rw [(NormedSpace.inclusionInDoubleDualLi 𝕜 (E := DFJPSum D)).norm_map] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_right
      hT (norm_nonneg ξ)).trans_eq (one_mul _))
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The interpolation space is reflexive whenever its generating set is
weakly compact. Completeness and its norm were constructed before this theorem. -/
theorem reflexive [CompleteSpace E]
    (hK : IsCompact ((toWeakSpace 𝕜 E) '' D.carrier)) :
    IsReflexiveNormedSpace 𝕜 (DFJPSpace D) := by
  intro ξ
  obtain ⟨x, hx⟩ := (inclusion_weaklyCompact D hK).bidual_mem_image ξ
  let f := ofSummable D x (summable_gauge_sq_of_bidual_image D ξ x hx)
  refine ⟨f, ?_⟩
  apply bidual_inclusion_injective D
  rw [bidualMap_inclusion]
  simpa [f] using hx

end DFJPSpace

end SurveyStatements.P4
