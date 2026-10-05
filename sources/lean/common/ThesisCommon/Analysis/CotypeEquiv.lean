import ThesisCommon.Analysis.CotypeIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Quadratic cotype passes through an actual Banach space isomorphism,
with the distortion recorded explicitly. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem HasRademacherCotype.two_of_equiv {C : ℝ}
    (h : HasRademacherCotype Y 2 C) (e : X ≃L[𝕜] Y) :
    HasRademacherCotype X 2
      (max 1 (C * ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)) := by
  let A := ‖e.toContinuousLinearMap‖
  let B := ‖e.symm.toContinuousLinearMap‖
  let D := max 1 (C * A * B)
  have hC : 0 ≤ C := zero_le_one.trans h.2.1
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨le_rfl, le_max_left _ _, ?_⟩
  intro n x
  let r (ε : Fin n → Bool) := ∑ i, if ε i then x i else -x i
  have hsum (ε : Fin n → Bool) :
      (∑ i, if ε i then e (x i) else -e (x i)) = e (r ε) := by
    simp only [r, map_sum, apply_ite, map_neg]
  have hx (i : Fin n) : ‖x i‖ ^ 2 ≤ B ^ 2 * ‖e (x i)‖ ^ 2 := by
    have hb : ‖x i‖ ≤ B * ‖e (x i)‖ := by
      have hb := e.symm.toContinuousLinearMap.le_opNorm (e (x i))
      change ‖e.symm (e (x i))‖ ≤ B * ‖e (x i)‖ at hb
      rwa [ContinuousLinearEquiv.symm_apply_apply] at hb
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr hb
    simpa only [mul_pow] using hsq
  have hr (ε : Fin n → Bool) : ‖e (r ε)‖ ^ 2 ≤ A ^ 2 * ‖r ε‖ ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hA (norm_nonneg _))).mpr (e.toContinuousLinearMap.le_opNorm (r ε))
    simpa only [mul_pow] using hsq
  have hbase := h.2.2 n (fun i => e (x i))
  simp only [Real.rpow_two, hsum] at hbase
  have houter : (∑ ε : Fin n → Bool, ‖e (r ε)‖ ^ 2) ≤
      A ^ 2 * ∑ ε : Fin n → Bool, ‖r ε‖ ^ 2 := by
    simpa only [Finset.mul_sum] using (Finset.sum_le_sum fun ε _ => hr ε)
  have hleft : (∑ i, ‖x i‖ ^ 2) ≤ B ^ 2 * ∑ i, ‖e (x i)‖ ^ 2 := by
    simpa only [Finset.mul_sum] using (Finset.sum_le_sum fun i _ => hx i)
  have hD : (C * A * B) ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg hC hA) hB)
      (zero_le_one.trans (le_max_left _ _))).mpr (le_max_right _ _)
  simp only [Real.rpow_two]
  change (∑ i, ‖x i‖ ^ (2 : ℕ)) ≤
    D ^ 2 * (2 ^ n : ℝ)⁻¹ * ∑ ε : Fin n → Bool, ‖r ε‖ ^ (2 : ℕ)
  calc
    _ ≤ B ^ 2 * (C ^ 2 * (2 ^ n : ℝ)⁻¹ * ∑ ε : Fin n → Bool, ‖e (r ε)‖ ^ 2) :=
      hleft.trans (mul_le_mul_of_nonneg_left hbase (sq_nonneg B))
    _ ≤ B ^ 2 * (C ^ 2 * (2 ^ n : ℝ)⁻¹ * (A ^ 2 * ∑ ε : Fin n → Bool, ‖r ε‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left houter (by positivity)) (sq_nonneg B)
    _ = (C * A * B) ^ 2 * (2 ^ n : ℝ)⁻¹ * ∑ ε : Fin n → Bool, ‖r ε‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end ThesisCommon
