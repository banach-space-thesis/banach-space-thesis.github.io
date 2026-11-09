import BanachIsometric.RawTensorComponents
import BanachIsometric.AlexanderWhitneySelectors

/-! The literal bidegree components of the boundary of the actual
Alexander--Whitney map. No differential identity is assumed. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawAlexanderWhitney_leftBoundary_component {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (a : ℚ) :
    rawTensorComponent X Y p q
      (rawTensorLeftBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ a))) =
      a • TensorProduct.map (rawBoundary p) LinearMap.id
        (awPureTerm σ (p + 1) q (by omega)) := by
  let F := (rawTensorComponent X Y p q).comp (rawTensorLeftBoundary X Y)
  have hsel := rawAlexanderWhitney_selecting_single F (by omega : (p + 1) + q = n + 1)
    (fun r s hne c => rawTensorComponent_left_inclusion_of_ne X Y hne c) σ a
  simpa only [F, LinearMap.comp_apply, rawTensorComponent_left_inclusion] using hsel

theorem rawAlexanderWhitney_rightBoundary_component {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (a : ℚ) :
    rawTensorComponent X Y p q
      (rawTensorRightBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ a))) =
      a • ((-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)
        (awPureTerm σ p (q + 1) (by omega))) := by
  let F := (rawTensorComponent X Y p q).comp (rawTensorRightBoundary X Y)
  have hsel := rawAlexanderWhitney_selecting_single F (by omega : p + (q + 1) = n + 1)
    (fun r s hne c => rawTensorComponent_right_inclusion_of_ne X Y hne c) σ a
  simpa only [F, LinearMap.comp_apply, rawTensorComponent_right_inclusion] using hsel

theorem rawAlexanderWhitney_totalBoundary_component {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) :
    rawTensorComponent X Y p q
      (rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ 1))) =
      TensorProduct.map (rawBoundary p) LinearMap.id (awPureTerm σ (p + 1) q (by omega)) +
        (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)
          (awPureTerm σ p (q + 1) (by omega)) := by
  simp only [rawTensorTotalBoundary, LinearMap.add_apply, map_add,
    rawAlexanderWhitney_leftBoundary_component X Y h,
    rawAlexanderWhitney_rightBoundary_component X Y h, one_smul]

theorem rawAlexanderWhitney_leftBoundary_component_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (a : ℚ) :
    rawTensorComponent X Y p q
      (rawTensorLeftBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ a))) = 0 := by
  apply rawAlexanderWhitney_zero_of_summands
    ((rawTensorComponent X Y p q).comp (rawTensorLeftBoundary X Y)) (n + 1) ?_ σ a
  intro r s hrs c
  apply rawTensorComponent_left_inclusion_of_ne X Y
  intro he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change r = p + 1 at h₁
  change s = q at h₂
  exact h (by omega)

theorem rawAlexanderWhitney_rightBoundary_component_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (σ : RawSingularSimplex (X × Y) (n + 1)) (a : ℚ) :
    rawTensorComponent X Y p q
      (rawTensorRightBoundary X Y (rawAlexanderWhitney (n + 1) (Finsupp.single σ a))) = 0 := by
  apply rawAlexanderWhitney_zero_of_summands
    ((rawTensorComponent X Y p q).comp (rawTensorRightBoundary X Y)) (n + 1) ?_ σ a
  intro r s hrs c
  apply rawTensorComponent_right_inclusion_of_ne X Y
  intro he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change r = p at h₁
  change s = q + 1 at h₂
  exact h (by omega)

end BanachIsometric.SingularAW
