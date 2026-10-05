import ThesisCommon.Analysis.SharpFactorization
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Mul

/-! Exact inverse bound for multiplication by a continuous coefficient of modulus at least 1/2. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]

def continuousMapHalfBoundInverse (a : C(K, 𝕜)) (ha : ∀ x, 1 / 2 ≤ ‖a x‖) : C(K, 𝕜) :=
  ⟨fun x => (a x)⁻¹, a.continuous.inv₀ (fun x => norm_pos_iff.mp
    ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (ha x)))⟩

theorem norm_continuousMapHalfBoundInverse_le (a : C(K, 𝕜)) (ha : ∀ x, 1 / 2 ≤ ‖a x‖) :
    ‖continuousMapHalfBoundInverse a ha‖ ≤ 2 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro x
  change ‖(a x)⁻¹‖ ≤ 2
  rw [norm_inv]
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (ha x)
  norm_num at h
  exact h

theorem continuousMap_multiplier_factors_two (a : C(K, 𝕜)) (ha : ∀ x, 1 / 2 ≤ ‖a x‖) :
    FactorsIdentityWith (ContinuousLinearMap.mul 𝕜 C(K, 𝕜) a) C(K, 𝕜) 2 := by
  let U := ContinuousLinearMap.mul 𝕜 C(K, 𝕜) (continuousMapHalfBoundInverse a ha)
  refine ⟨U, ContinuousLinearMap.id 𝕜 C(K, 𝕜), ?_, ?_⟩
  · ext g x
    change (a x)⁻¹ * (a x * g x) = g x
    rw [← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (ha x))), one_mul]
  · have hU : ‖U‖ ≤ 2 := (ContinuousLinearMap.opNorm_mul_apply_le 𝕜 C(K, 𝕜) _).trans
      (norm_continuousMapHalfBoundInverse_le a ha)
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg U)).trans
      (by simpa only [mul_one] using hU)

end ThesisCommon
