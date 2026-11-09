import BanachIsometric.AlexanderWhitneyMap

/-! Literal bidegree components of the concrete Alexander--Whitney map. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorComponent (p q : ℕ) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawTensorChains X Y p q :=
  DirectSum.component ℚ (ℕ × ℕ) (fun ij => RawTensorChains X Y ij.1 ij.2) (p, q)

@[simp] theorem rawTensorComponent_inclusion (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawTensorComponent X Y p q (rawTensorInclusion X Y p q c) = c := by
  simp only [rawTensorComponent, rawTensorInclusion, DirectSum.component.lof_self]

theorem rawTensorComponent_inclusion_of_ne {p q r s : ℕ} (h : (r, s) ≠ (p, q))
    (c : RawTensorChains X Y r s) :
    rawTensorComponent X Y p q (rawTensorInclusion X Y r s c) = 0 := by
  simp only [rawTensorComponent, rawTensorInclusion, DirectSum.component.of, h, dite_false]

theorem rawAlexanderWhitney_component_single {n p q : ℕ} (h : p + q = n)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    rawTensorComponent X Y p q (rawAlexanderWhitney n (Finsupp.single σ a)) =
      a • awPureTerm σ p q h := by
  classical
  rw [rawAlexanderWhitney_single, map_sum]
  simp only [map_smul]
  let z : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n} :=
    ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩
  rw [Finset.sum_eq_single z]
  · simp only [z, rawTensorComponent_inclusion]
  · intro ij _ hne
    have hv : ij.val ≠ (p, q) := by
      intro he
      exact hne (Subtype.ext he)
    rw [rawTensorComponent_inclusion_of_ne X Y hv, smul_zero]
  · intro hz
    exact (hz (Finset.mem_attach _ z)).elim

theorem rawAlexanderWhitney_component_single_of_ne {n p q : ℕ} (h : p + q ≠ n)
    (σ : RawSingularSimplex (X × Y) n) (a : ℚ) :
    rawTensorComponent X Y p q (rawAlexanderWhitney n (Finsupp.single σ a)) = 0 := by
  classical
  rw [rawAlexanderWhitney_single, map_sum]
  apply Finset.sum_eq_zero
  intro ij _
  have hv : ij.val ≠ (p, q) := by
    intro he
    have hm := Finset.mem_antidiagonal.mp ij.property
    rw [he] at hm
    exact h hm
  rw [map_smul, rawTensorComponent_inclusion_of_ne X Y hv, smul_zero]

theorem rawTensorComponent_left_inclusion (p q : ℕ)
    (c : RawTensorChains X Y (p + 1) q) :
    rawTensorComponent X Y p q
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y (p + 1) q c)) =
      TensorProduct.map (rawBoundary p) LinearMap.id c := by
  rw [rawTensorLeftBoundary_inclusion]
  change rawTensorComponent X Y p q
    (rawTensorInclusion X Y p q (TensorProduct.map (rawBoundary p) LinearMap.id c)) = _
  exact rawTensorComponent_inclusion X Y p q _

theorem rawTensorComponent_left_inclusion_of_ne {p q r s : ℕ}
    (h : (r, s) ≠ (p + 1, q)) (c : RawTensorChains X Y r s) :
    rawTensorComponent X Y p q
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y r s c)) = 0 := by
  rw [rawTensorLeftBoundary_inclusion]
  cases r with
  | zero => simp only [rawTensorLeftComponent, LinearMap.zero_apply, map_zero]
  | succ r =>
    change rawTensorComponent X Y p q
      (rawTensorInclusion X Y r s (TensorProduct.map (rawBoundary r) LinearMap.id c)) = 0
    apply rawTensorComponent_inclusion_of_ne X Y
    intro he
    exact h (by cases he; rfl)

theorem rawTensorComponent_right_inclusion (p q : ℕ)
    (c : RawTensorChains X Y p (q + 1)) :
    rawTensorComponent X Y p q
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y p (q + 1) c)) =
      (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q) c := by
  rw [rawTensorRightBoundary_inclusion]
  change rawTensorComponent X Y p q
    ((-1 : ℚ) ^ p • rawTensorInclusion X Y p q
      (TensorProduct.map LinearMap.id (rawBoundary q) c)) = _
  rw [map_smul, rawTensorComponent_inclusion]

theorem rawTensorComponent_right_inclusion_of_ne {p q r s : ℕ}
    (h : (r, s) ≠ (p, q + 1)) (c : RawTensorChains X Y r s) :
    rawTensorComponent X Y p q
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y r s c)) = 0 := by
  rw [rawTensorRightBoundary_inclusion]
  cases s with
  | zero => simp only [rawTensorRightComponent, LinearMap.zero_apply, map_zero]
  | succ s =>
    change rawTensorComponent X Y p q
      ((-1 : ℚ) ^ r • rawTensorInclusion X Y r s
        (TensorProduct.map LinearMap.id (rawBoundary s) c)) = 0
    rw [map_smul, rawTensorComponent_inclusion_of_ne X Y (show (r, s) ≠ (p, q) from ?_), smul_zero]
    intro he
    exact h (by cases he; rfl)

end BanachIsometric.SingularAW
