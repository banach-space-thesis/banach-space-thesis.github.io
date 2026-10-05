import ThesisCommon.Analysis.GowersMaureyToeplitzTailBlocks
import ThesisCommon.Analysis.GowersMaureyCoordinateIntervalBounds

/-! Normalized finite-band Laurent tests with controlled interval norm.
Every test is supported after an arbitrary prescribed cutoff. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def normalizedToeplitzTailVector (𝕜 : Type*) [RCLike 𝕜] (M r B : ℕ) (δ : ℝ) : C00 𝕜 :=
  (1+δ)⁻¹ • ((logarithmicWeight r / r) • toeplitzTailVector 𝕜 M r B)

theorem normalizedToeplitzTailVector_mem_afterCutoff (M r B : ℕ) (δ : ℝ) :
    normalizedToeplitzTailVector 𝕜 M r B δ ∈ afterCutoff B :=
  (afterCutoff B).smul_mem _ ((afterCutoff B).smul_mem _ (toeplitzTailVector_mem_afterCutoff M r B))

theorem normalizedToeplitzTailVector_intervalNorm_le (D : ConstructionData 𝕜)
    (M r B m n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hratio : (r : ℝ)/n ∈ Set.Icc (Real.log (D.j (2*m+1) : ℝ))
      (Real.exp (D.j (2*m+1) : ℝ)))
    (hf : logarithmicWeight r ≤ (1+δ) * logarithmicWeight ((r : ℝ)/n)) :
    intervalNorm D n (normalizedToeplitzTailVector 𝕜 M r B δ) ≤ 1 := by
  have hc : 0 < 1+δ := by positivity
  have ha : StrictMono (fun t : Fin r => B+1+(2*M+1)*t.val+M) := by
    intro t u htu
    exact Nat.add_lt_add_right (Nat.add_lt_add_left
      (Nat.mul_lt_mul_of_pos_left htu (by omega)) _) _
  have hh := normalized_single_sum_intervalNorm_le_one_add D ha m n hratio hδ hf
  change intervalNorm D n ((1+δ)⁻¹ • _) ≤ 1
  rw [seminorm_real_smul, abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (1+δ)⁻¹ * (1+δ) := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hc).le
    _ = 1 := inv_mul_cancel₀ hc.ne'

theorem denseEmbedding_real_smul (D : ConstructionData 𝕜) (c : ℝ) (x : C00 𝕜) :
    denseEmbedding D (c • x) = (c : 𝕜) • denseEmbedding D x := by
  have he : c • x = (c : 𝕜) • x := by
    ext n
    simp only [Finsupp.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  rw [he]
  exact map_smul (denseEmbedding D) (c : 𝕜) x

theorem normalizedToeplitzTailVector_image_norm_lower (D : ConstructionData 𝕜)
    (M r B : ℕ) (a : WienerSequences 𝕜)
    (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    (hr : 2 ≤ r) {δ : ℝ} (hδ : 0 ≤ δ) :
    (logarithmicWeight r / logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ)) * ‖a‖ / (1+δ) ≤
      ‖laurentOperator D a (denseEmbedding D (normalizedToeplitzTailVector 𝕜 M r B δ))‖ := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hfr : 0 ≤ logarithmicWeight r := zero_le_one.trans (one_le_logarithmicWeight (by omega))
  have hc : 0 < 1+δ := by positivity
  rw [normalizedToeplitzTailVector, denseEmbedding_real_smul, map_smul,
    norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc),
    denseEmbedding_real_smul, map_smul, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (div_nonneg hfr hrp.le)]
  calc
    _ = (1+δ)⁻¹ * ((logarithmicWeight r / r) *
        (((r : ℝ) / logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ)) * ‖a‖)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (laurent_tail_vector_norm_lower D M r B a hband hr)
        (div_nonneg hfr hrp.le)) (inv_pos.mpr hc).le

end ThesisCommon.GowersMaurey
