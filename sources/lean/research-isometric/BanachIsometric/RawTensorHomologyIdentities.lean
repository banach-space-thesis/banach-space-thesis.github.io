import BanachIsometric.RawTensorHomologyMaps
import BanachIsometric.RawTensorHomotopyMaps

/-! The actual tensor homology projection and inclusion satisfy p i = id
and i p = the previously contracted tensor projector. The two maps
intertwine the chain differential with zero. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorHomologyProjection_inclusion (n : ℕ) (a : RawHomologyTensorDegree X Y n) :
    rawTensorHomologyProjection X Y n (rawTensorHomologyInclusion X Y n a) = a := by
  have he : (rawTensorHomologyProjection X Y n).comp (rawTensorHomologyInclusion X Y n) =
      LinearMap.id := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, h⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorHomologyProjection X Y n
      (rawTensorHomologyInclusion X Y n (rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b))) =
        rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b)
    simp only [rawTensorHomologyInclusion_tmul, rawTensorHomologyProjection_tmul,
      rawFactorHomologyProjection_inclusion]
  exact LinearMap.congr_fun he a

theorem rawTensorHomologyInclusion_projection (n : ℕ) (a : rawTensorTotalDegree X Y n) :
    (rawTensorHomologyInclusion X Y n (rawTensorHomologyProjection X Y n a)).val =
      rawTensorBothProjector X Y a.val := by
  have he : (rawTensorTotalDegree X Y n).subtype.comp
      ((rawTensorHomologyInclusion X Y n).comp (rawTensorHomologyProjection X Y n)) =
        (rawTensorBothProjector X Y).comp (rawTensorTotalDegree X Y n).subtype := by
    apply rawTensorHomogeneous_linearMap_ext
    intro p q hpq σ τ
    simp only [LinearMap.comp_apply, rawTensorHomologyProjection_tmul, rawTensorHomologyInclusion_tmul]
    change rawTensorInclusion X Y p q
      (rawFactorHomologyInclusion X p (rawFactorHomologyProjection X p (Finsupp.single σ 1)) ⊗ₜ[ℚ]
        rawFactorHomologyInclusion Y q (rawFactorHomologyProjection Y q (Finsupp.single τ 1))) =
      rawTensorBothProjector X Y (rawTensorInclusion X Y p q
        (Finsupp.single σ 1 ⊗ₜ[ℚ] Finsupp.single τ 1))
    exact (rawTensorBothProjector_tmul X Y p q (Finsupp.single σ 1) (Finsupp.single τ 1)).symm
  exact LinearMap.congr_fun he a

theorem rawTensorHomologyProjectionTotal_boundary (n : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorHomologyProjectionTotal X Y n (rawTensorTotalBoundary X Y c) = 0 := by
  have he : (rawTensorHomologyProjectionTotal X Y n).comp (rawTensorTotalBoundary X Y) = 0 := by
    apply DirectSum.linearMap_ext
    rintro ⟨p, q⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorHomologyProjectionTotal X Y n
      (rawTensorTotalBoundary X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) = 0
    rw [rawTensorTotalBoundary, LinearMap.add_apply, map_add]
    have hleft : rawTensorHomologyProjectionTotal X Y n
        (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) = 0 := by
      cases p with
      | zero =>
        simp only [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, LinearMap.zero_apply, map_zero]
      | succ p =>
        rw [rawTensorLeftBoundary_tmul]
        by_cases h : p + q = n
        · simp only [rawTensorHomologyProjectionTotal_tmul X Y h,
            rawFactorHomologyProjection_boundary, TensorProduct.zero_tmul, map_zero]
        · exact rawTensorHomologyProjectionTotal_of_ne X Y h _
    have hright : rawTensorHomologyProjectionTotal X Y n
        (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (a ⊗ₜ[ℚ] b))) = 0 := by
      cases q with
      | zero =>
        simp only [rawTensorRightBoundary_inclusion, rawTensorRightComponent, LinearMap.zero_apply, map_zero]
      | succ q =>
        rw [rawTensorRightBoundary_tmul, map_smul]
        by_cases h : p + q = n
        · simp only [rawTensorHomologyProjectionTotal_tmul X Y h,
            rawFactorHomologyProjection_boundary, TensorProduct.tmul_zero, map_zero, smul_zero]
        · rw [rawTensorHomologyProjectionTotal_of_ne X Y h, smul_zero]
    rw [hleft, hright, add_zero]
  exact LinearMap.congr_fun he c

theorem rawTensorHomologyInclusion_cycle (n : ℕ) (c : RawHomologyTensorDegree X Y n) :
    rawTensorTotalBoundary X Y (rawTensorHomologyInclusion X Y n c).val = 0 := by
  have he : (rawTensorTotalBoundary X Y).comp
      ((rawTensorTotalDegree X Y n).subtype.comp (rawTensorHomologyInclusion X Y n)) = 0 := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨p, q⟩, h⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change rawTensorTotalBoundary X Y
      (rawTensorHomologyInclusion X Y n (rawHomologyTensorInclusion X Y h (a ⊗ₜ[ℚ] b))).val = 0
    rw [rawTensorHomologyInclusion_tmul]
    change rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q
        (rawFactorHomologyInclusion X p a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y q b)) +
      rawTensorRightBoundary X Y (rawTensorInclusion X Y p q
        (rawFactorHomologyInclusion X p a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y q b)) = 0
    have hleft : rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q
        (rawFactorHomologyInclusion X p a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y q b)) = 0 := by
      cases p with
      | zero => simp only [rawTensorLeftBoundary_inclusion, rawTensorLeftComponent, LinearMap.zero_apply]
      | succ p => simp only [rawTensorLeftBoundary_tmul, rawBoundary_factorHomologyInclusion,
          TensorProduct.zero_tmul, map_zero]
    have hright : rawTensorRightBoundary X Y (rawTensorInclusion X Y p q
        (rawFactorHomologyInclusion X p a ⊗ₜ[ℚ] rawFactorHomologyInclusion Y q b)) = 0 := by
      cases q with
      | zero => simp only [rawTensorRightBoundary_inclusion, rawTensorRightComponent, LinearMap.zero_apply]
      | succ q => simp only [rawTensorRightBoundary_tmul, rawBoundary_factorHomologyInclusion,
          TensorProduct.tmul_zero, map_zero, smul_zero]
    rw [hleft, hright, add_zero]
  exact LinearMap.congr_fun he c

end BanachIsometric.SingularAW
