import ThesisCommon.Analysis.GowersMaureyRIS
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The logarithmic cutoff in the literal RIS definition and the large-form
consequence of Gowers--Maurey's first RIS estimate. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem logarithmicWeight_inverse (r : ℝ) :
    logarithmicWeight ((2 : ℝ)^r - 1) = r := by
  rw [logarithmicWeight, sub_add_cancel, Real.log_rpow (by norm_num)]
  exact mul_div_cancel_right₀ r (ne_of_gt (Real.log_pos (by norm_num)))

theorem hasDerivAt_logarithmicWeight_one :
    HasDerivAt logarithmicWeight (1 / (2 * Real.log 2)) 1 := by
  convert (((hasDerivAt_id (1 : ℝ)).add_const 1).log (by norm_num)).div_const
    (Real.log 2) using 1
  norm_num
  ring

theorem ris_first_cutoff_eq (N : ℕ) (ε : ℝ) :
    (2 * N / deriv logarithmicWeight 1) * ((2 : ℝ)^((N : ℝ)^2 / ε^2) - 1) =
      (4 * N * Real.log 2) * ((2 : ℝ)^((N : ℝ)^2 / ε^2) - 1) := by
  rw [hasDerivAt_logarithmicWeight_one.deriv]
  simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_inv]
  ring

theorem logarithmic_large_size_ratio {N k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 0 < k) (hlarge : (2 : ℝ)^((N : ℝ)^2 / ε^2) - 1 ≤ k) :
    (N : ℝ) / Real.sqrt (logarithmicWeight k) ≤ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (N : ℝ)^2 / ε^2 ≤ logarithmicWeight k := by
    rw [logarithmicWeight, le_div_iff₀ hlog2]
    have hpow : (2 : ℝ)^((N : ℝ)^2 / ε^2) ≤ (k : ℝ) + 1 := by linarith
    have h := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hpow
    rwa [Real.log_rpow (by norm_num)] at h
  have hf : 0 < logarithmicWeight k := lt_of_lt_of_le zero_lt_one (one_le_logarithmicWeight hk)
  have hs : 0 < Real.sqrt (logarithmicWeight k) := Real.sqrt_pos.mpr hf
  have hsquare : (N : ℝ)^2 ≤ ε^2 * logarithmicWeight k := by
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hlog
    nlinarith
  have hroot : (N : ℝ) ≤ ε * Real.sqrt (logarithmicWeight k) := by
    have hsquare' : (N : ℝ)^2 ≤ (ε * Real.sqrt (logarithmicWeight k))^2 := by
      simpa only [mul_pow, Real.sq_sqrt hf.le] using hsquare
    exact (sq_le_sq₀ (Nat.cast_nonneg N) (mul_nonneg hε.le hs.le)).mp hsquare'
  exact (div_le_iff₀ hs).mpr hroot

/-- The final assertion of source Lemma 1, including equality at the cutoff. -/
theorem RISData.form_bound_of_large_size {D : ConstructionData 𝕜} {N : ℕ} {ε : ℝ}
    {x : Fin N → C00 𝕜} (h : RISData D ε x) {k : ℕ} (hk : 2 ≤ k)
    {weight : ℝ} (hw : Real.sqrt (logarithmicWeight k) ≤ weight)
    {a : C00 𝕜} (ha : IsForm D k weight a)
    (hlarge : (2 : ℝ)^((N : ℝ)^2 / ε^2) - 1 ≤ k) :
    ‖pairing a (∑ i, x i)‖ ≤ 1 + 2 * ε := by
  have hmain := h.form_bound hk hw ha
  have hratio := logarithmic_large_size_ratio h.epsilon_pos (by omega : 0 < k) hlarge
  linarith

end ThesisCommon.GowersMaurey
