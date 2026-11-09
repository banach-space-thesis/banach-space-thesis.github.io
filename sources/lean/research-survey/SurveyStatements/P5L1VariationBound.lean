import SurveyStatements.P5L1VariationImages

/-! A uniform finite-branch variation estimate for actual bounded scalar
Haar multipliers on L¹. The proof tests the operator on normalized dyadic
leaf indicators and uses no Semenov–Uksusov hypothesis or axiom. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem multiplier_symbol_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
    (n : ℕ) (k : Fin (2 ^ n)) : ‖d n k‖ ≤ ‖D‖ := by
  have hh : ‖lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k‖ = intervalLpDyadicRadius n := by
    simpa using lpHaarDyadic_norm 𝕜 ⟨1, le_rfl⟩ (by norm_num) n k k.isLt
  have hb := D.le_opNorm (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
  rw [hD, norm_smul, hh] at hb
  have hp := intervalLpDyadicRadius_pos n
  nlinarith

namespace DyadicBranch
variable {r : ℕ} (B : DyadicBranch r) (𝕜 : Type*) [RCLike 𝕜]
  (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
  (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
  (hD : ∀ (n : ℕ) (k : Fin (2 ^ n)),
    D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) = d n k • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)

include hD

theorem leafTest_image_annulus_integral (N j : ℕ) (hj : j < N) :
    (∫ x in B.annulus j, ‖D (B.leafTest 𝕜 N) x‖
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        ‖defect (B.symbol 𝕜 d) j‖ / 2 := by
  rw [setIntegral_congr_ae (B.annulus_measurable j)
    ((B.leafTest_image_on_annulus 𝕜 D d hD N j hj).mono
      (fun x hx hxmem => congrArg norm (hx hxmem))), setIntegral_const, smul_eq_mul,
    B.annulus_real_measure, norm_mul, norm_pow]
  have ht : ‖(2 : 𝕜)‖ = 2 := by norm_num
  rw [ht]
  have hc : (2 : ℝ) ^ (r + j) * intervalLpDyadicRadius (r + j) = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using lpHaarRadius_cancel (r + j)
  calc
    intervalLpDyadicRadius (r + j) / 2 *
        ((2 : ℝ) ^ (r + j) * ‖defect (B.symbol 𝕜 d) j‖) =
      ((2 : ℝ) ^ (r + j) * intervalLpDyadicRadius (r + j)) *
        ‖defect (B.symbol 𝕜 d) j‖ / 2 := by ring
    _ = _ := by rw [hc]; ring

theorem finite_defect_sum_le (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖defect (B.symbol 𝕜 d) j‖) ≤ 4 * ‖D‖ := by
  have h := B.sum_annulus_integral_norm_le 𝕜 N (D (B.leafTest 𝕜 N))
  have he : (∑ j ∈ Finset.range N, ∫ x in B.annulus j, ‖D (B.leafTest 𝕜 N) x‖
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        (∑ j ∈ Finset.range N, ‖defect (B.symbol 𝕜 d) j‖) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    exact B.leafTest_image_annulus_integral 𝕜 D d hD N j (Finset.mem_range.mp hj)
  rw [he] at h
  have hbound : ‖D (B.leafTest 𝕜 N)‖ ≤ 2 * ‖D‖ := by
    calc
      _ ≤ ‖D‖ * ‖B.leafTest 𝕜 N‖ := D.le_opNorm _
      _ ≤ ‖D‖ * 2 := mul_le_mul_of_nonneg_left (B.leafTest_norm_le 𝕜 N) (norm_nonneg D)
      _ = _ := by ring
  linarith

theorem finite_variation_le (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) ≤ 6 * ‖D‖ := by
  have hv := finite_variation_le_defect_sum (B.symbol 𝕜 d) N
  have hd := B.finite_defect_sum_le 𝕜 D d hD (N + 1)
  linarith

end DyadicBranch
end SurveyStatements.P5L1Variation
