import SurveyStatements.P4DFJPReflexivity

/-! The actual bounded factor map into the DFJP interpolation space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048

open Set Metric

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {X : Type w} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace DFJPSpace

variable (D : DFJPGaugeData 𝕜 E) (T : X →L[𝕜] E)
variable (hT : ∀ x : X, ‖x‖ ≤ 1 → T x ∈ D.carrier)

include hT

lemma operator_mem_range (x : X) : T x ∈ Set.range (inclusion D) := by
  let r : ℝ := ‖x‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a : 𝕜 := r
  have ha : a ≠ 0 := by simpa [a] using hr.ne'
  have hna : ‖a‖ = r := by simp [a, abs_of_pos hr]
  have hx : ‖a⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, ← div_eq_inv_mul]
    apply (div_le_one hr).mpr
    dsimp [r]
    linarith
  refine ⟨a • ofMem D (hT (a⁻¹ • x) hx), ?_⟩
  rw [map_smul, inclusion_ofMem, map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]

def liftLinearMap : X →ₗ[𝕜] DFJPSpace D := by
  classical
  choose f hf using operator_mem_range D T hT
  exact
    { toFun := f
      map_add' := by
        intro x y
        apply inclusion_injective D
        simp only [map_add, hf]
      map_smul' := by
        intro a x
        apply inclusion_injective D
        simp only [RingHom.id_apply, map_smul, hf] }

@[simp] lemma inclusion_liftLinearMap (x : X) :
    inclusion D (liftLinearMap D T hT x) = T x := by
  dsimp [liftLinearMap]
  exact Classical.choose_spec (operator_mem_range D T hT x)

lemma norm_liftLinearMap_unitBall (x : X) (hx : ‖x‖ ≤ 1) :
    ‖liftLinearMap D T hT x‖ ≤ Real.sqrt ((4 / 3 : ℝ) * (1 + D.normBound ^ 2)) := by
  have heq : liftLinearMap D T hT x = ofMem D (hT x hx) :=
    inclusion_injective D (by simp)
  rw [heq]
  exact norm_ofMem_le D (hT x hx)

lemma norm_liftLinearMap_le (x : X) :
    ‖liftLinearMap D T hT x‖ ≤
      Real.sqrt ((4 / 3 : ℝ) * (1 + D.normBound ^ 2)) * ‖x‖ := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  let a : 𝕜 := ‖x‖
  have ha : a ≠ 0 := by simpa [a] using (norm_ne_zero_iff.mpr hxzero)
  have hna : ‖a‖ = ‖x‖ := by simp [a]
  have hunit : ‖a⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hna, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxzero)]
  have heq : a • liftLinearMap D T hT (a⁻¹ • x) = liftLinearMap D T hT x := by
    rw [← map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [← heq, norm_smul, hna]
  exact (mul_le_mul_of_nonneg_left
    (norm_liftLinearMap_unitBall D T hT (a⁻¹ • x) hunit) (norm_nonneg x)).trans_eq
      (mul_comm _ _)

def lift : X →L[𝕜] DFJPSpace D :=
  (liftLinearMap D T hT).mkContinuous
    (Real.sqrt ((4 / 3 : ℝ) * (1 + D.normBound ^ 2))) (norm_liftLinearMap_le D T hT)

@[simp] lemma inclusion_comp_lift : (inclusion D).comp (lift D T hT) = T := by
  ext x
  exact inclusion_liftLinearMap D T hT x

end DFJPSpace

end SurveyStatements.P4
