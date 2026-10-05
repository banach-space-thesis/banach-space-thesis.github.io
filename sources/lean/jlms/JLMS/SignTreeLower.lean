import JLMS.EllOneFiniteLower

/-!
# Finite sign trees force an ℓ¹ embedding over either scalar field

Near-real sign values suffice even for complex coefficients: rotate by 1
or -i so that the total absolute real part is at least half the ℓ¹ mass.
The sign error costs at most one quarter of that mass. Dual norms at most
two then give the uniform lower constant 1/8. This is the final finite
estimate needed by the scalar-uniform Hagler–Johnson construction.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem rclike_norm_I_le_one : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
  by_cases hI : (RCLike.I : 𝕜) = 0
  · simp [hI]
  · exact (RCLike.norm_I_of_ne_zero hI).le

theorem rclike_norm_le_abs_parts (z : 𝕜) :
    ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  conv_lhs => rw [← RCLike.re_add_im z]
  calc
    _ ≤ ‖(RCLike.re z : 𝕜)‖ + ‖(RCLike.im z : 𝕜) * RCLike.I‖ := norm_add_le _ _
    _ ≤ |RCLike.re z| + |RCLike.im z| := by
      rw [RCLike.norm_ofReal, norm_mul, RCLike.norm_ofReal]
      exact add_le_add_left (by
        simpa using mul_le_mul_of_nonneg_left (rclike_norm_I_le_one (𝕜 := 𝕜)) (abs_nonneg (RCLike.im z))) _

theorem exists_rotation_real_mass (F : Finset ℕ) (a : ℕ → 𝕜) :
    ∃ ζ : 𝕜, ‖ζ‖ ≤ 1 ∧
      (∑ n ∈ F, ‖a n‖) / 2 ≤ ∑ n ∈ F, |RCLike.re (ζ * a n)| := by
  have hmass : (∑ n ∈ F, ‖a n‖) ≤
      (∑ n ∈ F, |RCLike.re (a n)|) + ∑ n ∈ F, |RCLike.im (a n)| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun n hn => rclike_norm_le_abs_parts _)
  by_cases h : (∑ n ∈ F, ‖a n‖) / 2 ≤ ∑ n ∈ F, |RCLike.re (a n)|
  · exact ⟨1, by simp, by simpa using h⟩
  · refine ⟨-RCLike.I, by simpa using (rclike_norm_I_le_one (𝕜 := 𝕜)), ?_⟩
    simp only [neg_mul, map_neg, RCLike.I_mul_re, neg_neg]
    linarith

theorem real_mul_near_sign_lower (a t : 𝕜)
    (ht : ‖t - (if 0 ≤ RCLike.re a then (1 : 𝕜) else -1)‖ ≤ 1 / 4) :
    |RCLike.re a| - ‖a‖ / 4 ≤ RCLike.re (a * t) := by
  let σ : 𝕜 := if 0 ≤ RCLike.re a then 1 else -1
  change ‖t - σ‖ ≤ 1 / 4 at ht
  have he : RCLike.re (a * σ) = |RCLike.re a| := by
    dsimp [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have herr : |RCLike.re (a * (t - σ))| ≤ ‖a‖ / 4 := by
    calc
      _ ≤ ‖a * (t - σ)‖ := RCLike.abs_re_le_norm _
      _ = ‖a‖ * ‖t - σ‖ := norm_mul _ _
      _ ≤ ‖a‖ / 4 := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left ht (norm_nonneg a)
  have hsplit : RCLike.re (a * t) = RCLike.re (a * σ) + RCLike.re (a * (t - σ)) := by
    rw [← map_add]
    congr 1
    ring
  rw [hsplit, he]
  linarith [(abs_le.mp herr).1]

def FiniteSignTree (v : ℕ → X) : Prop :=
  ∀ F : Finset ℕ, ∀ σ : ℕ → Bool,
    ∃ φ : X →L[𝕜] 𝕜, ‖φ‖ ≤ 2 ∧
      ∀ n ∈ F, ‖φ (v n) - (if σ n then (1 : 𝕜) else -1)‖ ≤ 1 / 4

theorem finiteSignTree_lower (v : ℕ → X) (h : FiniteSignTree (𝕜 := 𝕜) v)
    (F : Finset ℕ) (a : ℕ → 𝕜) :
    (1 / 8 : ℝ) * (∑ n ∈ F, ‖a n‖) ≤ ‖∑ n ∈ F, a n • v n‖ := by
  classical
  obtain ⟨ζ, hζ, hmass⟩ := exists_rotation_real_mass F a
  let σ (n : ℕ) : Bool := decide (0 ≤ RCLike.re (ζ * a n))
  obtain ⟨φ, hφ, he⟩ := h F σ
  have hscalar (n : ℕ) (hn : n ∈ F) :
      |RCLike.re (ζ * a n)| - ‖a n‖ / 4 ≤ RCLike.re ((ζ * a n) * φ (v n)) := by
    have hnorm : ‖ζ * a n‖ ≤ ‖a n‖ := by
      rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_right hζ (norm_nonneg (a n))
    have hh := real_mul_near_sign_lower (ζ * a n) (φ (v n)) (by simpa [σ] using he n hn)
    linarith
  have hsum := Finset.sum_le_sum hscalar
  have hvalue : RCLike.re (φ (ζ • (∑ n ∈ F, a n • v n))) =
      ∑ n ∈ F, RCLike.re ((ζ * a n) * φ (v n)) := by
    simp only [Finset.smul_sum, smul_smul, map_sum, map_smul, smul_eq_mul]
  have hupper : RCLike.re (φ (ζ • (∑ n ∈ F, a n • v n))) ≤
      2 * ‖∑ n ∈ F, a n • v n‖ := by
    calc
      _ ≤ ‖φ (ζ • (∑ n ∈ F, a n • v n))‖ := RCLike.re_le_norm _
      _ ≤ ‖φ‖ * ‖ζ • (∑ n ∈ F, a n • v n)‖ := φ.le_opNorm _
      _ ≤ 2 * ‖ζ • (∑ n ∈ F, a n • v n)‖ :=
        mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
      _ ≤ 2 * ‖∑ n ∈ F, a n • v n‖ := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (by
          simpa using mul_le_mul_of_nonneg_right hζ (norm_nonneg (∑ n ∈ F, a n • v n))) (by norm_num)
  rw [hvalue] at hupper
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div] at hsum
  linarith

theorem containsEllOne_of_finiteSignTree [CompleteSpace X] (v : ℕ → X)
    (hv : ∀ n, ‖v n‖ ≤ 1) (h : FiniteSignTree (𝕜 := 𝕜) v) : ContainsEllOne 𝕜 X :=
  containsEllOne_of_finite_lower v zero_le_one hv (by norm_num) (finiteSignTree_lower v h)

end JLMS
