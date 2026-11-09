import BanachIsometric.RawTensorBicomplex

/-! The signed total boundary of the actual raw tensor bicomplex squares
to zero. The cross terms cancel with the actual Koszul sign. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorLeftBoundary_squared :
    (rawTensorLeftBoundary X Y).comp (rawTensorLeftBoundary X Y) = 0 := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorLeftBoundary X Y
    (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) = 0
  cases p with
  | zero => simp [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent]
  | succ p =>
    cases p with
    | zero => simp [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent,
        TensorProduct.map_tmul]
    | succ p =>
      rw [rawTensorLeftBoundary_tmul, rawTensorLeftBoundary_tmul]
      have hz := LinearMap.congr_fun (rawBoundary_squared (X := X) p) c
      change rawBoundary p (rawBoundary (p + 1) c) = 0 at hz
      rw [hz, TensorProduct.zero_tmul, map_zero]

theorem rawTensorRightBoundary_squared :
    (rawTensorRightBoundary X Y).comp (rawTensorRightBoundary X Y) = 0 := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorRightBoundary X Y
    (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) = 0
  cases q with
  | zero => simp [rawTensorRightBoundary_inclusion, rawTensorRightComponent]
  | succ q =>
    cases q with
    | zero => simp [rawTensorRightBoundary_inclusion, rawTensorRightComponent,
        TensorProduct.map_tmul]
    | succ q =>
      rw [rawTensorRightBoundary_tmul, map_smul, rawTensorRightBoundary_tmul]
      have hz := LinearMap.congr_fun (rawBoundary_squared (X := Y) q) d
      change rawBoundary q (rawBoundary (q + 1) d) = 0 at hz
      rw [hz, TensorProduct.tmul_zero, map_zero, smul_zero, smul_zero]

theorem rawTensorBoundaries_anticommute :
    (rawTensorLeftBoundary X Y).comp (rawTensorRightBoundary X Y) +
      (rawTensorRightBoundary X Y).comp (rawTensorLeftBoundary X Y) = 0 := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawTensorLeftBoundary X Y
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) +
    rawTensorRightBoundary X Y
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) = 0
  cases p with
  | zero =>
    cases q <;> simp [rawTensorLeftBoundary_inclusion, rawTensorRightBoundary_inclusion,
      rawTensorLeftComponent, rawTensorRightComponent, TensorProduct.map_tmul]
  | succ p =>
    cases q with
    | zero => simp [rawTensorLeftBoundary_inclusion, rawTensorRightBoundary_inclusion,
        rawTensorLeftComponent, rawTensorRightComponent, TensorProduct.map_tmul]
    | succ q =>
      rw [rawTensorRightBoundary_tmul, map_smul, rawTensorLeftBoundary_tmul,
        rawTensorLeftBoundary_tmul, rawTensorRightBoundary_tmul]
      rw [← add_smul]
      have hc : (-1 : ℚ) ^ (p + 1) + (-1 : ℚ) ^ p = 0 := by
        rw [pow_succ, mul_neg_one, neg_add_cancel]
      rw [hc, zero_smul]

theorem rawTensorTotalBoundary_squared :
    (rawTensorTotalBoundary X Y).comp (rawTensorTotalBoundary X Y) = 0 := by
  apply LinearMap.ext
  intro c
  change rawTensorLeftBoundary X Y
      (rawTensorLeftBoundary X Y c + rawTensorRightBoundary X Y c) +
    rawTensorRightBoundary X Y
      (rawTensorLeftBoundary X Y c + rawTensorRightBoundary X Y c) = 0
  rw [map_add, map_add]
  have hL := LinearMap.congr_fun (rawTensorLeftBoundary_squared X Y) c
  have hR := LinearMap.congr_fun (rawTensorRightBoundary_squared X Y) c
  change rawTensorLeftBoundary X Y (rawTensorLeftBoundary X Y c) = 0 at hL
  change rawTensorRightBoundary X Y (rawTensorRightBoundary X Y c) = 0 at hR
  rw [hL, hR, zero_add, add_zero]
  exact LinearMap.congr_fun (rawTensorBoundaries_anticommute X Y) c

end BanachIsometric.SingularAW
