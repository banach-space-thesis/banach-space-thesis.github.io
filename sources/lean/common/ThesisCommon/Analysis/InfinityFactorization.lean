import ThesisCommon.Analysis.InfinityRestriction
import ThesisCommon.Analysis.InfinityInterference
import ThesisCommon.Analysis.SequenceEntryAlgebra
import ThesisCommon.Analysis.SharpFactorization
import ThesisCommon.Analysis.ScalarPFP

/-! The basis-style proof of 2-plus-PFP for actual scalar ell_infinity.
First obtain a support on which the matrix series represents the operator;
only then use small off-diagonal row sums to estimate the whole operator.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinity_compression_hasSum
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    {M : Set ℕ}
    (hrep : ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) →
      HasSum (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) (T x m))
    (f : ℕ ↪ ℕ) (hf : ∀ k, f k ∈ M) (x : lp (fun _ : ℕ => 𝕜) ∞) (i : ℕ) :
    HasSum (fun j => x j * T (lp.single ∞ (f j) (1 : 𝕜)) (f i))
      ((((lpRestrict ∞ f).comp T).comp (lpExtend ∞ f)) x i) := by
  let y := lpExtend (𝕜 := 𝕜) ∞ f x
  have hy (n : ℕ) (hn : n ∉ M) : y n = 0 :=
    lpExtend_apply_off_range f x (by rintro ⟨j, rfl⟩; exact hn (hf j))
  have h := hrep (f i) y hy
  have hoff (n : ℕ) (hn : n ∉ Set.range f) :
      y n * T (lp.single ∞ n (1 : 𝕜)) (f i) = 0 := by
    rw [show y n = 0 from lpExtend_apply_off_range f x hn, zero_mul]
  have hh := (f.injective.hasSum_iff hoff).mpr h
  simpa only [Function.comp_def, y, lpExtend_apply_image] using hh

theorem infinity_diagonalPart_scalar_apply
    (S : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    (x : lp (fun _ : ℕ => 𝕜) ∞) (i : ℕ) :
    lpDiagonalPart S x i = x i * S (lp.single ∞ i (1 : 𝕜)) i := by
  rw [lpDiagonalPart_apply, lpEntry_apply]
  have heq : (lp.single ∞ i (x i) : lp (fun _ : ℕ => 𝕜) ∞) =
      x i • lp.single ∞ i (1 : 𝕜) := by rw [← lp.single_smul]; simp
  rw [heq, map_smul]
  rfl

theorem infinity_diagonal_compression
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) {η : ℝ} (hη : 0 < η) :
    ∃ f : ℕ ↪ ℕ, ‖((lpRestrict ∞ f).comp T).comp (lpExtend ∞ f) -
      lpDiagonalPart (((lpRestrict ∞ f).comp T).comp (lpExtend ∞ f))‖ < η := by
  classical
  obtain ⟨M, _, hM, hrep⟩ := infinity_matrix_restriction T
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  obtain ⟨f, _, hfM, hsmall⟩ := bounded_finite_sums_small_off_diagonal (norm_nonneg T)
    (infinity_images_have_bounded_finite_sums T) hM (show 0 < η / 2 by positivity)
  let S := ((lpRestrict (𝕜 := 𝕜) ∞ f).comp T).comp (lpExtend ∞ f)
  let R := S - lpDiagonalPart S
  have hdiag (x : lp (fun _ : ℕ => 𝕜) ∞) (i : ℕ) :
      lpDiagonalPart S x i = x i * T (lp.single ∞ (f i) (1 : 𝕜)) (f i) := by
    rw [infinity_diagonalPart_scalar_apply]
    change x i * T (lpExtend (𝕜 := 𝕜) ∞ f (lp.single ∞ i (1 : 𝕜))) (f i) = _
    rw [lpExtend_single]
  have hR : ‖R‖ ≤ η / 2 := by
    apply R.opNorm_le_bound (by positivity)
    intro x
    apply lp.norm_le_of_forall_le (by positivity)
    intro i
    have hs : HasSum (fun j => if j = i then 0 else
        x j * T (lp.single ∞ (f j) (1 : 𝕜)) (f i)) (R x i) := by
      have hh := (infinity_compression_hasSum T hrep f hfM x i).sub
        (hasSum_ite_eq i (x i * T (lp.single ∞ (f i) (1 : 𝕜)) (f i)))
      convert hh using 1
      · funext j
        by_cases hji : j = i <;> simp [hji]
      · change S x i - lpDiagonalPart S x i = _
        rw [hdiag]
    have hnorm : ‖R x i‖ ≤ ‖x‖ *
        ∑' j, if j = i then 0 else ‖T (lp.single ∞ (f j) (1 : 𝕜)) (f i)‖ := by
      apply hs.norm_le_of_bounded ((hsmall i).1.hasSum.mul_left ‖x‖)
      intro j
      by_cases hji : j = i
      · simp only [if_pos hji, norm_zero, mul_zero, le_refl]
      · simp only [if_neg hji, norm_mul]
        exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x j) (norm_nonneg _)
    calc
      _ ≤ ‖x‖ * ∑' j, if j = i then 0 else ‖T (lp.single ∞ (f j) (1 : 𝕜)) (f i)‖ := hnorm
      _ ≤ ‖x‖ * (η / 2) := mul_le_mul_of_nonneg_left (hsmall i).2.le (norm_nonneg _)
      _ = _ := mul_comm _ _
  exact ⟨f, hR.trans_lt (by linarith)⟩

/-- The full source result. The matrix representation and every analytic
input to the perturbation assembly have been proved for the actual space. -/
theorem infinity_hasCPlusPFP_two : HasCPlusPFP 𝕜 (lp (fun _ : ℕ => 𝕜) ∞) 2 := by
  apply hasCPlusPFP_of_approximate_compressions (by norm_num : (0 : ℝ) < 2) IsLpDiagonal
  · exact fun D hD => lp_diagonal_dichotomy (by norm_num) scalar_hasCPFP_two D hD
  · intro T η hη
    obtain ⟨f, hf⟩ := infinity_diagonal_compression T hη
    exact ⟨lpRestrict ∞ f, lpExtend ∞ f,
      lpDiagonalPart (((lpRestrict ∞ f).comp T).comp (lpExtend ∞ f)),
      lpRestrict_comp_extend f, norm_lpRestrict_le f, norm_lpExtend_le f,
      isLpDiagonal_lpDiagonalPart _, hf⟩

end ThesisCommon
