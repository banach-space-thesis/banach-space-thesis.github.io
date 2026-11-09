import SurveyStatements.P5L1VariationEndpoints

/-! Finite local branch estimates. Only the finitely many tested Haar vectors
must be eigenvectors. No infinite multiplier extension is a hypothesis. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

theorem single_haar_symbol_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (n : ℕ) (k : Fin (2 ^ n)) (a : 𝕜)
    (hD : D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      a • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) : ‖a‖ ≤ ‖D‖ := by
  have hh : ‖lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k‖ = intervalLpDyadicRadius n := by
    simpa using lpHaarDyadic_norm 𝕜 ⟨1, le_rfl⟩ (by norm_num) n k k.isLt
  have hb := D.le_opNorm (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k)
  rw [hD, norm_smul, hh] at hb
  have hp := intervalLpDyadicRadius_pos n
  nlinarith

namespace DyadicBranch
variable {r : ℕ} (B : DyadicBranch r) (𝕜 : Type*) [RCLike 𝕜]

theorem density_difference_image_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜) (j : ℕ) (a : 𝕜)
    (hD : D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      a • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    D (B.density 𝕜 (j + 1) - B.density 𝕜 j) =
      a • (B.density 𝕜 (j + 1) - B.density 𝕜 j) := by
  have hval : (B.index (j + 1)).val / 2 = (B.index j).val :=
    congrArg Fin.val (B.parent j)
  have hchild : (B.index (j + 1)).val = 2 * (B.index j).val ∨
      (B.index (j + 1)).val = 2 * (B.index j).val + 1 := by omega
  change D (cellDensity 𝕜 ((r + j) + 1) (B.index (j + 1)) -
    cellDensity 𝕜 (r + j) (B.index j)) = _
  change _ = a • (cellDensity 𝕜 ((r + j) + 1) (B.index (j + 1)) -
    cellDensity 𝕜 (r + j) (B.index j))
  rcases hchild with h | h
  · rw [h, cellDensity_left_difference, map_smul, hD]
    exact smul_comm _ _ _
  · rw [h, cellDensity_right_difference, map_smul, hD]
    exact smul_comm _ _ _

theorem leafTest_image_eq_sum_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    D (B.leafTest 𝕜 N) = ∑ j ∈ Finset.range N,
      B.symbol 𝕜 d j • (B.density 𝕜 (j + 1) - B.density 𝕜 j) := by
  rw [B.leafTest_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact B.density_difference_image_local 𝕜 D j (B.symbol 𝕜 d j)
    (hD j (Finset.mem_range.mp hj))

theorem leafTest_image_on_annulus_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j))
    (j : ℕ) (hj : j < N) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ B.annulus j →
      D (B.leafTest 𝕜 N) x =
        (2 : 𝕜) ^ (r + j) * defect (B.symbol 𝕜 d) j := by
  rw [B.leafTest_image_eq_sum_local 𝕜 D d N hD]
  have hterms : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ i : ℕ,
      (B.symbol 𝕜 d i • (B.density 𝕜 (i + 1) - B.density 𝕜 i)) x =
        B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (B.symbol 𝕜 d i)
        (B.density 𝕜 (i + 1) - B.density 𝕜 i),
      Lp.coeFn_sub (B.density 𝕜 (i + 1)) (B.density 𝕜 i)] with x hsmul hsub
    simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hsub] using hsmul
  have hvalues : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ i : ℕ,
      x ∈ B.annulus j → B.density 𝕜 i x =
        if i ≤ j then (2 : 𝕜) ^ (r + i) else 0 :=
    ae_all_iff.mpr (fun i => B.density_on_annulus 𝕜 i j)
  filter_upwards [lpHaar_coeFn_finset_sum (Finset.range N)
      (fun i => B.symbol 𝕜 d i • (B.density 𝕜 (i + 1) - B.density 𝕜 i)),
    hterms, hvalues] with x hsum hterm hvalue hx
  rw [hsum]
  simp_rw [hterm]
  have hzero : ∀ i ∈ Finset.range N, i ∉ Finset.range (j + 1) →
      B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) = 0 := by
    intro i _ hi
    have hi' : j < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    rw [hvalue (i + 1) hx, hvalue i hx, if_neg (by omega), if_neg (by omega)]
    ring
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hj)) hzero,
    Finset.sum_range_succ]
  have hbefore : ∀ i ∈ Finset.range j,
      B.symbol 𝕜 d i * (B.density 𝕜 (i + 1) x - B.density 𝕜 i x) =
        (2 : 𝕜) ^ (r + i) * B.symbol 𝕜 d i := by
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    rw [hvalue (i + 1) hx, hvalue i hx, if_pos (by omega), if_pos hi'.le]
    change _ = (2 : 𝕜) ^ (r + i) * B.symbol 𝕜 d i
    rw [show r + (i + 1) = (r + i) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hbefore, hvalue (j + 1) hx, hvalue j hx,
    if_neg (by omega), if_pos le_rfl, ← prefixAverage_weighted_sum]
  simp only [defect]
  ring


theorem leafTest_image_annulus_integral_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j))
    (j : ℕ) (hj : j < N) :
    (∫ x in B.annulus j, ‖D (B.leafTest 𝕜 N) x‖
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        ‖defect (B.symbol 𝕜 d) j‖ / 2 := by
  rw [setIntegral_congr_ae (B.annulus_measurable j)
    ((B.leafTest_image_on_annulus_local 𝕜 D d N hD j hj).mono
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

theorem finite_defect_sum_le_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    (∑ j ∈ Finset.range N, ‖defect (B.symbol 𝕜 d) j‖) ≤ 4 * ‖D‖ := by
  have h := B.sum_annulus_integral_norm_le 𝕜 N (D (B.leafTest 𝕜 N))
  have he : (∑ j ∈ Finset.range N, ∫ x in B.annulus j, ‖D (B.leafTest 𝕜 N) x‖
      ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        (∑ j ∈ Finset.range N, ‖defect (B.symbol 𝕜 d) j‖) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    exact B.leafTest_image_annulus_integral_local 𝕜 D d N hD j (Finset.mem_range.mp hj)
  rw [he] at h
  have hbound : ‖D (B.leafTest 𝕜 N)‖ ≤ 2 * ‖D‖ := by
    calc
      _ ≤ ‖D‖ * ‖B.leafTest 𝕜 N‖ := D.le_opNorm _
      _ ≤ ‖D‖ * 2 := mul_le_mul_of_nonneg_left (B.leafTest_norm_le 𝕜 N) (norm_nonneg D)
      _ = _ := by ring
  linarith

theorem finite_variation_le_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N + 1, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    (∑ j ∈ Finset.range N,
      ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) ≤ 6 * ‖D‖ := by
  have hv := finite_variation_le_defect_sum (B.symbol 𝕜 d) N
  have hd := B.finite_defect_sum_le_local 𝕜 D d (N + 1) hD
  linarith

theorem finite_variation_endpoints_le_local
    (D : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (N : ℕ)
    (hD : ∀ j < N + 1, D (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) =
      B.symbol 𝕜 d j • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ (r + j) (B.index j)) :
    ‖B.symbol 𝕜 d 0‖ + (∑ j ∈ Finset.range N,
      ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) +
        ‖B.symbol 𝕜 d N‖ ≤ 8 * ‖D‖ := by
  have hv := B.finite_variation_le_local 𝕜 D d N hD
  have hroot := single_haar_symbol_norm_le 𝕜 D (r + 0) (B.index 0)
    (B.symbol 𝕜 d 0) (hD 0 (by omega))
  have hend := single_haar_symbol_norm_le 𝕜 D (r + N) (B.index N)
    (B.symbol 𝕜 d N) (hD N (by omega))
  linarith

end DyadicBranch

theorem single_meanZero_extension_haar (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (n : ℕ) (k : Fin (2 ^ n)) (a : 𝕜)
    (hR : R (meanZeroHaar 𝕜 n k) = a • meanZeroHaar 𝕜 n k) :
    extendMeanZero 𝕜 R (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) =
      a • lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k := by
  change (R (intervalLpMeanZeroProjection 𝕜 ⟨1, le_rfl⟩
    (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k))).val = _
  rw [meanZeroProjection_haar, hR]
  rfl

theorem meanZero_finite_variation_endpoints_le_local (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜)
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    {r : ℕ} (B : DyadicBranch r) (N : ℕ)
    (hR : ∀ j < N + 1, R (meanZeroHaar 𝕜 (r + j) (B.index j)) =
      B.symbol 𝕜 d j • meanZeroHaar 𝕜 (r + j) (B.index j)) :
    ‖B.symbol 𝕜 d 0‖ + (∑ j ∈ Finset.range N,
      ‖B.symbol 𝕜 d (j + 1) - B.symbol 𝕜 d j‖) +
        ‖B.symbol 𝕜 d N‖ ≤ 16 * ‖R‖ := by
  have hv := B.finite_variation_endpoints_le_local 𝕜 (extendMeanZero 𝕜 R) d N
    (fun j hj => single_meanZero_extension_haar 𝕜 R (r + j) (B.index j)
      (B.symbol 𝕜 d j) (hR j hj))
  have hn := extendMeanZero_norm_le 𝕜 R
  linarith

end SurveyStatements.P5L1Variation

