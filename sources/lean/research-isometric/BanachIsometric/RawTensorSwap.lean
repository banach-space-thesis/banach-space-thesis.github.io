import BanachIsometric.RawTensorMapChain

/-! The actual tensor swap includes the Koszul sign and interchanges the
two signed factor boundaries. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorSwap : RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains Y X :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains Y X) (fun ij =>
    (-1 : ℚ) ^ (ij.1 * ij.2) • (rawTensorInclusion Y X ij.2 ij.1).comp
      (TensorProduct.comm ℚ (RawRationalChains X ij.1) (RawRationalChains Y ij.2)).toLinearMap)

@[simp] theorem rawTensorSwap_tmul (p q : ℕ)
    (a : RawRationalChains X p) (b : RawRationalChains Y q) :
    rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)) =
      (-1 : ℚ) ^ (p * q) • rawTensorInclusion Y X q p (b ⊗ₜ[ℚ] a) := by
  simp only [rawTensorSwap, rawTensorInclusion, DirectSum.toModule_lof, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul]

private theorem rationalParitySign_sq (p : ℕ) : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 := by
  calc
    _ = ((-1 : ℚ) * (-1)) ^ p := (mul_pow _ _ _).symm
    _ = 1 := by simp only [neg_mul_neg, one_mul, one_pow]

theorem rawTensorSwap_involutive (c : RawBigradedTensorChains X Y) :
    rawTensorSwap Y X (rawTensorSwap X Y c) = c := by
  have h : (rawTensorSwap Y X).comp (rawTensorSwap X Y) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    rintro ⟨p, q⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorSwap Y X (rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) =
      rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)
    have hs : (-1 : ℚ) ^ (p * q) * (-1 : ℚ) ^ (q * p) = 1 := by
      rw [Nat.mul_comm q p, rationalParitySign_sq]
    simp only [rawTensorSwap_tmul, map_smul, smul_smul, hs, one_smul]
  exact LinearMap.congr_fun h c

theorem rawTensorSwap_leftBoundary :
    (rawTensorSwap X Y).comp (rawTensorLeftBoundary X Y) =
      (rawTensorRightBoundary Y X).comp (rawTensorSwap X Y) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change rawTensorSwap X Y (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) =
    rawTensorRightBoundary Y X (rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)))
  cases p with
  | zero =>
    simp only [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, LinearMap.zero_apply, map_zero,
      rawTensorSwap_tmul, map_smul, rawTensorRightBoundary_inclusion, rawTensorRightComponent, smul_zero]
  | succ p =>
    have hs : (-1 : ℚ) ^ ((p + 1) * q) * (-1 : ℚ) ^ q = (-1 : ℚ) ^ (p * q) := by
      rw [Nat.succ_mul, pow_add, mul_assoc, rationalParitySign_sq, mul_one]
    simp only [rawTensorLeftBoundary_tmul, rawTensorSwap_tmul, map_smul,
      rawTensorRightBoundary_tmul, smul_smul, hs]

theorem rawTensorSwap_rightBoundary :
    (rawTensorSwap X Y).comp (rawTensorRightBoundary X Y) =
      (rawTensorLeftBoundary Y X).comp (rawTensorSwap X Y) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change rawTensorSwap X Y (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) =
    rawTensorLeftBoundary Y X (rawTensorSwap X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b)))
  cases q with
  | zero =>
    simp only [rawTensorRightBoundary_inclusion, rawTensorRightComponent, LinearMap.zero_apply, map_zero,
      rawTensorSwap_tmul, map_smul, rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, smul_zero]
  | succ q =>
    have hs : (-1 : ℚ) ^ p * (-1 : ℚ) ^ (p * q) = (-1 : ℚ) ^ (p * (q + 1)) := by
      rw [Nat.mul_succ, pow_add]
      exact mul_comm _ _
    simp only [rawTensorRightBoundary_tmul, map_smul, rawTensorSwap_tmul, smul_smul,
      rawTensorLeftBoundary_tmul, hs]

theorem rawTensorSwap_boundary (c : RawBigradedTensorChains X Y) :
    rawTensorSwap X Y (rawTensorTotalBoundary X Y c) =
      rawTensorTotalBoundary Y X (rawTensorSwap X Y c) := by
  have hL := LinearMap.congr_fun (rawTensorSwap_leftBoundary X Y) c
  have hR := LinearMap.congr_fun (rawTensorSwap_rightBoundary X Y) c
  simp only [LinearMap.comp_apply] at hL hR
  change rawTensorSwap X Y (rawTensorLeftBoundary X Y c + rawTensorRightBoundary X Y c) =
    rawTensorLeftBoundary Y X (rawTensorSwap X Y c) + rawTensorRightBoundary Y X (rawTensorSwap X Y c)
  rw [map_add, hL, hR, add_comm]

end BanachIsometric.SingularAW
