import BanachIsometric.AlexanderWhitneyBoundaryComponents
import BanachIsometric.AlexanderWhitneyTensorBoundary
import BanachIsometric.RawTensorBoundarySquared

/-! The actual Alexander--Whitney differential identity on raw rational
singular chains. Its proof uses the literal front/back face restrictions and
the actual signed cancellation; no chain-map premise is supplied. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawAlexanderWhitney_boundary_component {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    rawTensorComponent X Y p q
      (rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ 1))) =
      rawTensorComponent X Y p q (rawAlexanderWhitney n (rawBoundary n (Finsupp.single σ 1))) := by
  subst n
  rw [rawAlexanderWhitney_totalBoundary_component X Y rfl,
    awPureTerm_leftBoundary rfl, awPureTerm_rightBoundary rfl]
  have hRat := rat_neg_one_pow_smul p
    (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • awRightFaceTerm (n := p + q) rfl σ j)
  rw [hRat, aw_signed_tensor_boundary]
  simp only [rawBoundary_single, map_sum, map_zsmul,
    rawAlexanderWhitney_component_single X Y rfl, one_smul]

theorem rawAlexanderWhitney_boundary_component_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    rawTensorComponent X Y p q
      (rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ 1))) =
      rawTensorComponent X Y p q (rawAlexanderWhitney n (rawBoundary n (Finsupp.single σ 1))) := by
  simp only [rawTensorTotalBoundary, LinearMap.add_apply, map_add,
    rawAlexanderWhitney_leftBoundary_component_of_ne X Y h,
    rawAlexanderWhitney_rightBoundary_component_of_ne X Y h, zero_add,
    rawBoundary_single, map_sum, map_zsmul,
    rawAlexanderWhitney_component_single_of_ne X Y h, smul_zero, Finset.sum_const_zero]

theorem rawAlexanderWhitney_boundary_single (n : ℕ)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ 1)) =
      rawAlexanderWhitney n (rawBoundary n (Finsupp.single σ 1)) := by
  apply DirectSum.ext_component ℚ
  rintro ⟨p, q⟩
  change rawTensorComponent X Y p q _ = rawTensorComponent X Y p q _
  by_cases h : p + q = n
  · exact rawAlexanderWhitney_boundary_component h σ
  · exact rawAlexanderWhitney_boundary_component_of_ne h σ

theorem rawAlexanderWhitney_boundary (n : ℕ) :
    (rawTensorTotalBoundary X Y).comp (rawAlexanderWhitney (n + 1)) =
      (rawAlexanderWhitney n).comp (rawBoundary n) := by
  apply Finsupp.lhom_ext
  intro σ a
  have hsingle : Finsupp.single σ a = a • Finsupp.single σ 1 := by simp
  rw [hsingle]
  simp only [map_smul, LinearMap.comp_apply]
  exact congrArg (fun c => a • c) (rawAlexanderWhitney_boundary_single n σ)

theorem rawAlexanderWhitney_boundary_zero :
    (rawTensorTotalBoundary X Y).comp (rawAlexanderWhitney (X := X) (Y := Y) 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  change rawTensorTotalBoundary X Y (rawAlexanderWhitney 0 (Finsupp.single σ a)) = 0
  apply rawAlexanderWhitney_zero_of_summands (rawTensorTotalBoundary X Y) 0 ?_ σ a
  intro r s hrs c
  have hr : r = 0 := by omega
  have hs : s = 0 := by omega
  subst r
  subst s
  rw [rawTensorTotalBoundary_inclusion]
  simp only [rawTensorLeftComponent, rawTensorRightComponent, LinearMap.zero_apply, add_zero]

theorem rawAlexanderWhitneyDiagonal_boundary (n : ℕ) :
    (rawTensorTotalBoundary X X).comp (rawAlexanderWhitneyDiagonal (X := X) (n + 1)) =
      (rawAlexanderWhitneyDiagonal (X := X) n).comp (rawBoundary n) := by
  let δ : C(X, X × X) := ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩
  change (rawTensorTotalBoundary X X).comp
      ((rawAlexanderWhitney (n + 1)).comp (rawChainMap δ (n + 1))) =
    ((rawAlexanderWhitney n).comp (rawChainMap δ n)).comp (rawBoundary n)
  rw [← LinearMap.comp_assoc, rawAlexanderWhitney_boundary, LinearMap.comp_assoc,
    rawChainMap_boundary, ← LinearMap.comp_assoc]

theorem rawAlexanderWhitneyDiagonal_boundary_zero :
    (rawTensorTotalBoundary X X).comp (rawAlexanderWhitneyDiagonal (X := X) 0) = 0 := by
  rw [rawAlexanderWhitneyDiagonal, ← LinearMap.comp_assoc,
    rawAlexanderWhitney_boundary_zero, LinearMap.zero_comp]

end BanachIsometric.SingularAW
