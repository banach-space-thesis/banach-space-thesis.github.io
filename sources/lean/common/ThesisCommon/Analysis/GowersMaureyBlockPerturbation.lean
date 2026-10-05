import ThesisCommon.Analysis.GowersMaureyBlockCoefficients
import ThesisCommon.Analysis.GowersMaureyLaurentTailTests
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Summable approximation errors transfer to the actual real block
span. Contractive interval restrictions control each coefficient, so the
bound is relative to the norm of the whole block sum, independently of
its number of terms. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_real_block_sum_near_subspace (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (u : ℕ → C00 𝕜) (v : ℕ → ShiftSpace D)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hunorm : ∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i))
    (hv : ∀ i, v i ∈ E) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i, ‖denseEmbedding D (u i)-v i‖ ≤ ε i)
    (s : Finset ℕ) (c : ℕ → ℝ) {δ : ℝ} (hsum : ∑ i ∈ s, ε i ≤ δ/2) :
    ∃ y ∈ E, ‖denseEmbedding D (∑ i ∈ s, c i • u i)-y‖ ≤
      δ * implicitNorm D (∑ i ∈ s, c i • u i) := by
  let x := ∑ i ∈ s, c i • u i
  let y := ∑ i ∈ s, (c i : 𝕜) • v i
  have hy : y ∈ E := E.sum_mem (fun i _ => E.smul_mem _ (hv i))
  refine ⟨y, hy, ?_⟩
  have he : denseEmbedding D x = ∑ i ∈ s, (c i : 𝕜) • denseEmbedding D (u i) := by
    simp only [x, map_sum, denseEmbedding_real_smul]
  change ‖denseEmbedding D x-y‖ ≤ δ * implicitNorm D x
  rw [he]
  change ‖(∑ i ∈ s, (c i : 𝕜) • denseEmbedding D (u i)) -
    (∑ i ∈ s, (c i : 𝕜) • v i)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖(c i : 𝕜) • denseEmbedding D (u i) - (c i : 𝕜) • v i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, |c i| * ‖denseEmbedding D (u i)-v i‖ := by
      simp only [← smul_sub, norm_smul, RCLike.norm_ofReal]
    _ ≤ ∑ i ∈ s, (2 * implicitNorm D x) * ε i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (mul_le_mul_of_nonneg_left (herr i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (abs_real_block_coefficient_le_twice D hu s c hi (hunorm i)) (hε i))
    _ = (2 * implicitNorm D x) * ∑ i ∈ s, ε i := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * implicitNorm D x) * (δ/2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) (apply_nonneg _ _))
    _ = δ * implicitNorm D x := by ring

theorem real_block_span_near_subspace (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (u : ℕ → C00 𝕜) (v : ℕ → ShiftSpace D)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hunorm : ∀ i, (1 : ℝ)/2 ≤ implicitNorm D (u i))
    (hv : ∀ i, v i ∈ E) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (herr : ∀ i, ‖denseEmbedding D (u i)-v i‖ ≤ ε i)
    {δ : ℝ} (hsum : ∀ s : Finset ℕ, ∑ i ∈ s, ε i ≤ δ/2) :
    ∀ x ∈ Submodule.span ℝ (Set.range u), ∃ y ∈ E,
      ‖denseEmbedding D x-y‖ ≤ δ * implicitNorm D x := by
  intro x hx
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  exact finite_real_block_sum_near_subspace D E u v hu hunorm hv ε hε herr
    c.support (fun i => c i) (hsum c.support)

theorem lower_bound_transfer_to_near_vector (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) {c δ : ℝ} (hc : 0 ≤ c)
    (x y : ShiftSpace D) (hy : c * ‖y‖ ≤ ‖T y‖)
    (hnear : ‖x-y‖ ≤ δ * ‖x‖) :
    (c - (c+‖T‖)*δ) * ‖x‖ ≤ ‖T x‖ := by
  have hx := norm_le_insert' x y
  have hxmul := mul_le_mul_of_nonneg_left hx hc
  have hTy := norm_le_insert' (T y) (T x)
  have hop := T.le_opNorm (x-y)
  rw [map_sub] at hop
  rw [norm_sub_rev (T y) (T x)] at hTy
  have hnear' := mul_le_mul_of_nonneg_left hnear (add_nonneg hc (norm_nonneg T))
  nlinarith

end ThesisCommon.GowersMaurey
