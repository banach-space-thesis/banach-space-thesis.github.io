import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Operator.Basic

/-! The actual finite absolutely convex orbit, with its coefficient budget.
This set contains precisely the finite combinations with sum of scalar norms
bounded by the prescribed radius. No operator approximation is assumed. -/
noncomputable section
open scoped BigOperators Pointwise
namespace ThesisCommon
variable {𝕜 X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [Fintype ι]

def finiteAbsoluteConvexOrbit (v : ι → X) (m : ℝ) : Set X :=
  {x | ∃ c : ι → 𝕜, (∑ i, ‖c i‖) ≤ m ∧ (∑ i, c i • v i) = x}

theorem zero_mem_finiteAbsoluteConvexOrbit (v : ι → X) {m : ℝ} (hm : 0 ≤ m) :
    (0 : X) ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp only [norm_zero, Finset.sum_const_zero]
    exact hm
  · simp

theorem smul_mem_finiteAbsoluteConvexOrbit (v : ι → X) {m : ℝ}
    (i : ι) (c : 𝕜) (hc : ‖c‖ ≤ m) :
    c • v i ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m := by
  classical
  refine ⟨Pi.single i c, ?_, ?_⟩
  · have hsum : (∑ j : ι, ‖(Pi.single i c : ι → 𝕜) j‖) = ‖c‖ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji]
      · simp
    exact hsum.trans_le hc
  · simp

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

theorem convex_finiteAbsoluteConvexOrbit (v : ι → X) (m : ℝ) :
    Convex ℝ (finiteAbsoluteConvexOrbit (𝕜 := 𝕜) v m) := by
  classical
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩ a b ha hb hab
  refine ⟨fun i => a • c i + b • d i, ?_, ?_⟩
  · calc
      (∑ i, ‖a • c i + b • d i‖) ≤
          ∑ i, (a * ‖c i‖ + b * ‖d i‖) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb] using norm_add_le (a • c i) (b • d i)
      _ = a * (∑ i, ‖c i‖) + b * (∑ i, ‖d i‖) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * m + b * m := add_le_add
        (mul_le_mul_of_nonneg_left hc ha) (mul_le_mul_of_nonneg_left hd hb)
      _ = m := by rw [← add_mul, hab, one_mul]
  · simp only [add_smul, smul_assoc, Finset.sum_add_distrib, Finset.smul_sum]

end ThesisCommon
