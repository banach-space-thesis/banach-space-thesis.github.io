import JLMS.CZeroFamilyImage

/-!
# Coordinate functions on the compact family image

Each coordinate of the compact image is a continuous scalar function,
automatically in C₀. Pullback gives the original extended function, and its
supremum norm is at most the original function's norm.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
variable (f : ℕ → CZero 𝕜 K)

def cZeroFamilyCoordinate (n : ℕ) : CZero 𝕜 (CZeroFamilyImage f) where
  toFun v := v.val n
  continuous_toFun := (continuous_apply n).comp continuous_subtype_val
  zero_at_infty' := by simp

@[simp] theorem cZeroFamilyCoordinate_imageMap (n : ℕ) (x : OnePoint K) :
    cZeroFamilyCoordinate f n (cZeroFamilyImageMap f x) = extendCZeroOnePoint (f n) x := rfl

theorem norm_cZeroFamilyCoordinate_le (n : ℕ) : ‖cZeroFamilyCoordinate f n‖ ≤ ‖f n‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (f n))).mpr
  intro v
  obtain ⟨x, rfl⟩ := cZeroFamilyImageMap_surjective f v
  change ‖cZeroFamilyCoordinate f n (cZeroFamilyImageMap f x)‖ ≤ ‖f n‖
  rw [cZeroFamilyCoordinate_imageMap]
  induction x using OnePoint.rec with
  | infty => change ‖(0 : 𝕜)‖ ≤ ‖f n‖; simpa using norm_nonneg (f n)
  | coe x => exact norm_CZero_apply_le (f n) x

end JLMS
