import PL1.EnfloMaxMass
import PL1.LpInterpolation
import PL1.NoiseHypercontractivity

/-! # Finite maximum bounds from the actual noise Lp-to-L2 contraction -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PL1.EnfloBush
open Walsh Noise NoiseHypercontractivity

theorem maxAbs_sq_le_energy (n : ℕ) (a : ℕ → ℝ) :
    maxAbs n a ^ 2 ≤ FiniteRademacherClipping.energy n a := by
  induction n with
  | zero => simp [maxAbs, FiniteRademacherClipping.energy]
  | succ n ih =>
    rw [maxAbs, FiniteRademacherClipping.energy_succ]
    by_cases h : maxAbs n a ≤ |a n|
    · rw [max_eq_right h, sq_abs]
      nlinarith [FiniteRademacherClipping.energy_nonneg n a]
    · rw [max_eq_left (le_of_not_ge h)]
      nlinarith [sq_nonneg (a n)]

theorem memLp_maxAbs (n : ℕ) (f : ℕ → Lp ℝ 2 haar) :
    MemLp (fun x => maxAbs n (fun j => f j x)) 2 haar := by
  induction n with
  | zero => exact MemLp.zero
  | succ n ih => exact ih.sup (Lp.memLp (f n)).abs

def maxL2 (n : ℕ) (f : ℕ → Lp ℝ 2 haar) : Lp ℝ 2 haar :=
  (memLp_maxAbs n f).toLp (fun x => maxAbs n (fun j => f j x))

theorem maxL2_coe (n : ℕ) (f : ℕ → Lp ℝ 2 haar) :
    maxL2 n f =ᵐ[haar] (fun x => maxAbs n (fun j => f j x)) :=
  (memLp_maxAbs n f).coeFn_toLp

theorem norm_l2_sq_eq_integral (f : Lp ℝ 2 haar) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂haar := by
  simpa only [ENNReal.toReal_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_one, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    norm_sq_eq_integral_rpow ℝ 2 (by norm_num) f (Filter.EventuallyEq.rfl : f =ᵐ[haar] f)

theorem integrable_l2_sq (f : Lp ℝ 2 haar) : Integrable (fun x => f x ^ 2) haar := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

theorem maxMass_l2_eq (n : ℕ) (f : ℕ → Lp ℝ 2 haar) :
    maxMass n (fun j => l2ToL1 (f j)) = ‖l2ToL1 (maxL2 n f)‖ := by
  rw [maxMass, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun j => ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) (f j)),
    ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) (maxL2 n f), maxL2_coe n f] with x hf hm he
  rw [hm, he, Real.norm_eq_abs, abs_of_nonneg (maxAbs_nonneg n _)]
  exact maxAbs_congr (fun j _ => hf j)

theorem maxMass_l2_sq_le (n : ℕ) (f : ℕ → Lp ℝ 2 haar) :
    maxMass n (fun j => l2ToL1 (f j)) ^ 2 ≤ ∑ j ∈ Finset.range n, ‖f j‖ ^ 2 := by
  have hnorm : ‖l2ToL1 (maxL2 n f)‖ ≤ ‖maxL2 n f‖ :=
    ProbabilityLp.norm_inclusionFun_le haar 1 2 (by norm_num) _
  rw [maxMass_l2_eq]
  apply (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
  rw [norm_l2_sq_eq_integral]
  have he : (fun x => maxL2 n f x ^ 2) =ᵐ[haar]
      (fun x => maxAbs n (fun j => f j x) ^ 2) := by
    filter_upwards [maxL2_coe n f] with x hx
    rw [hx]
  have hi : Integrable (fun x => maxAbs n (fun j => f j x) ^ 2) haar :=
    (integrable_l2_sq (maxL2 n f)).congr he
  rw [integral_congr_ae he]
  have h := integral_mono hi (integrable_finsetSum _ (fun j _ => integrable_l2_sq (f j)))
    (fun x => maxAbs_sq_le_energy n (fun j => f j x))
  rw [integral_finsetSum _ (fun j _ => integrable_l2_sq (f j))] at h
  simpa only [← norm_l2_sq_eq_integral] using h

theorem rpow_sq_eq (x a : ℝ) (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx]
  congr 1
  ring

theorem rpow_le_bound_mul {x A r : ℝ} (hx : 0 ≤ x) (hxA : x ≤ A) (hr : 0 ≤ r) :
    x ^ (r + 1) ≤ A ^ r * x := by
  rw [Real.rpow_add_of_nonneg hx hr zero_le_one, Real.rpow_one]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxA hr) hx

theorem positiveTimeNoiseL2_bounded_sq_le (u : ℝ≥0) (f : Lp ℝ 1 haar)
    (M : ℝ) (hM : 0 ≤ M) (hfM : ∀ᵐ x ∂haar, ‖f x‖ ≤ M)
    (hf : MemLp (fun x => f x) (exponent u) haar) :
    ‖positiveTimeNoiseL2 ℝ u (hf.toLp (fun x => f x))‖ ^ 2 ≤
      M ^ (2 * (1 - 1 / (exponent u).toReal)) * ‖f‖ ^ (2 / (exponent u).toReal) := by
  have h₁ : ‖positiveTimeNoiseL2 ℝ u (hf.toLp (fun x => f x))‖ ≤ ‖hf.toLp (fun x => f x)‖ := by
    calc
      _ ≤ ‖positiveTimeNoiseL2 ℝ u‖ * ‖hf.toLp (fun x => f x)‖ :=
        (positiveTimeNoiseL2 ℝ u).le_opNorm _
      _ ≤ 1 * ‖hf.toLp (fun x => f x)‖ := mul_le_mul_of_nonneg_right
        (norm_positiveTimeNoiseL2_le_one ℝ u) (norm_nonneg _)
      _ = _ := one_mul _
  have h₂ := LpInterpolation.norm_toLp_le_of_ae_norm_bound f (exponent u)
    (exponent_ge_one u) (exponent_ne_top u) M hM hfM hf
  have h := pow_le_pow_left₀ (norm_nonneg _) (h₁.trans h₂) 2
  rw [mul_pow, rpow_sq_eq M _ hM, rpow_sq_eq ‖f‖ _ (norm_nonneg _)] at h
  simpa only [mul_one_div] using h

/-- Uniform finite-family estimate for actual constant-rate noise. No
dimension appears in the constant; the small L1 mass carries a positive
power at every positive noise time. -/
theorem bounded_family_noise_max_sq_le (u : ℝ≥0) (n : ℕ) (f : ℕ → Lp ℝ 1 haar)
    (M : ℝ) (hM : 0 ≤ M) (hfM : ∀ j, ∀ᵐ x ∂haar, ‖f j x‖ ≤ M)
    (A C : ℝ) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hfA : ∀ j < n, ‖f j‖ ≤ A) (hfC : (∑ j ∈ Finset.range n, ‖f j‖) ≤ C) :
    maxMass n (fun j => noiseL1 ℝ constantRates u (f j)) ^ 2 ≤
      M ^ (2 * (1 - 1 / (exponent u).toReal)) * A ^ (2 / (exponent u).toReal - 1) * C := by
  let p := exponent u
  have hp (j : ℕ) : MemLp (fun x => f j x) p haar :=
    LpInterpolation.memLp_of_ae_norm_bound (f j) p (exponent_ge_one u) (exponent_ne_top u) M (hfM j)
  let F : ℕ → Lp ℝ 2 haar := fun j => positiveTimeNoiseL2 ℝ u ((hp j).toLp (fun x => f j x))
  have hF (j : ℕ) : l2ToL1 (F j) = noiseL1 ℝ constantRates u (f j) := by
    dsimp only [F]
    rw [positiveTimeNoiseL2_overlap]
    congr 1
    apply Lp.ext
    exact (ProbabilityLp.coeFn_inclusion haar 1 p (exponent_ge_one u) _).trans (hp j).coeFn_toLp
  have h := maxMass_l2_sq_le n F
  simp_rw [hF] at h
  apply h.trans
  have hp0 : 0 < p.toReal := by rw [exponent_toReal]; positivity
  have hr : 0 ≤ 2 / p.toReal - 1 := by
    have hp2 := exponent_toReal_le_two u
    have he : 1 ≤ 2 / p.toReal := (le_div_iff₀ hp0).mpr (by simpa only [one_mul] using hp2)
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range n, M ^ (2 * (1 - 1 / p.toReal)) * ‖f j‖ ^ (2 / p.toReal) :=
      Finset.sum_le_sum (fun j _ => positiveTimeNoiseL2_bounded_sq_le u (f j) M hM (hfM j) (hp j))
    _ ≤ ∑ j ∈ Finset.range n, M ^ (2 * (1 - 1 / p.toReal)) *
        (A ^ (2 / p.toReal - 1) * ‖f j‖) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM _)
      have hh := rpow_le_bound_mul (norm_nonneg (f j)) (hfA j (Finset.mem_range.mp hj)) hr
      simpa only [sub_add_cancel] using hh
    _ = (M ^ (2 * (1 - 1 / p.toReal)) * A ^ (2 / p.toReal - 1)) *
        ∑ j ∈ Finset.range n, ‖f j‖ := by simp only [← mul_assoc, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfC (mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hA _))

#print axioms bounded_family_noise_max_sq_le
end PL1.EnfloBush
