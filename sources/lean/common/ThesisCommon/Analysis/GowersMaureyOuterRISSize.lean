import ThesisCommon.Analysis.GowersMaureySourceTangent

/-! The first outer RIS size in the special-pair construction.
The floor of the square root of the printed initial size is already
larger than the actual RIS first-size threshold. Only the original
rapid sequence conditions are used. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem ris_size_threshold_add_one_le_exp {x : ℝ} (hx : 1 ≤ x) :
    (4 * x * Real.log 2) * ((2 : ℝ) ^ (x ^ 2) - 1) + 1 ≤
      Real.exp (6 * x ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hA0 : 0 ≤ 4 * x * Real.log 2 := by positivity
  have hA : 4 * x * Real.log 2 ≤ Real.exp (4 * x ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hlog1 (by positivity : 0 ≤ 4 * x)
    have hh := Real.add_one_le_exp (4 * x ^ 2)
    nlinarith
  have hB : (2 : ℝ) ^ (x ^ 2) ≤ Real.exp (x ^ 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  have hprod : (4 * x * Real.log 2) * ((2 : ℝ) ^ (x ^ 2) - 1) ≤
      Real.exp (5 * x ^ 2) := by
    calc
      _ ≤ (4 * x * Real.log 2) * (2 : ℝ) ^ (x ^ 2) := by nlinarith
      _ ≤ Real.exp (4 * x ^ 2) * Real.exp (x ^ 2) :=
        mul_le_mul hA hB (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h1 : 1 ≤ Real.exp (5 * x ^ 2) := Real.one_le_exp (by positivity)
  have h2 : 2 ≤ Real.exp (x ^ 2) := by linarith [Real.add_one_le_exp (x ^ 2)]
  calc
    _ ≤ Real.exp (5 * x ^ 2) + 1 := by linarith
    _ ≤ Real.exp (5 * x ^ 2) * Real.exp (x ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (5 * x ^ 2)).le]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)

theorem outer_initial_log_size_gt {k : ℕ} (hk : 0 < k) :
    12 * (k : ℝ) ^ 2 < Real.log (D.j (2 * k - 1) : ℝ) := by
  have hj0 : 0 < D.j 0 := D.j_positive 0
  have hprev := D.j_strict.add_le_nat (2 * k - 2) 0
  simp only [Nat.add_zero] at hprev
  have hkprev : k ≤ D.j (2 * k - 2) := by omega
  have hkprevR : (k : ℝ) ≤ D.j (2 * k - 2) := by exact_mod_cast hkprev
  have ha : 4 ≤ (D.j (2 * k - 2) : ℝ) := by
    have h := D.size_large (2 * k - 2)
    linarith
  have ha2 : 12 ≤ (D.j (2 * k - 2) : ℝ) ^ 2 := by nlinarith
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ k) hkprevR 2
  have hpower : 12 * (k : ℝ) ^ 2 ≤ (D.j (2 * k - 2) : ℝ) ^ 8 := by
    calc
      _ ≤ 12 * (D.j (2 * k - 2) : ℝ) ^ 2 := by linarith
      _ ≤ (D.j (2 * k - 2) : ℝ) ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg (D.j (2 * k - 2) : ℝ))]
      _ ≤ _ := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ D.j (2 * k - 2)) (by norm_num)
  have hg := D.size_pow_eight_lt_loglog (by omega : 2 * k - 2 < 2 * k - 1)
  exact hpower.trans_lt (hg.trans_le (Real.log_le_self
    (Real.log_nonneg (D.one_le_size (2 * k - 1)))))

theorem outer_ris_threshold_add_one_lt_sqrt {k : ℕ} (hk : 0 < k) :
    (4 * (k : ℝ) * Real.log 2) * ((2 : ℝ) ^ ((k : ℝ) ^ 2) - 1) + 1 <
      Real.sqrt (D.j (2 * k - 1) : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hJ : (0 : ℝ) < D.j (2 * k - 1) := by exact_mod_cast D.j_positive _
  have he : (Real.exp (6 * (k : ℝ) ^ 2)) ^ 2 < D.j (2 * k - 1) := by
    calc
      _ = Real.exp (12 * (k : ℝ) ^ 2) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      _ < Real.exp (Real.log (D.j (2 * k - 1) : ℝ)) :=
        Real.exp_lt_exp.mpr (D.outer_initial_log_size_gt hk)
      _ = _ := Real.exp_log hJ
  exact (ris_size_threshold_add_one_le_exp hk1).trans_lt
    ((Real.lt_sqrt (Real.exp_pos _).le).mpr he)

theorem outer_ris_floor_size_gt {k : ℕ} (hk : 0 < k) :
    (4 * (k : ℝ) * Real.log 2) * ((2 : ℝ) ^ ((k : ℝ) ^ 2) - 1) <
      (⌊Real.sqrt (D.j (2 * k - 1) : ℝ)⌋₊ : ℝ) := by
  have h := D.outer_ris_threshold_add_one_lt_sqrt hk
  have hf := Nat.lt_floor_add_one (Real.sqrt (D.j (2 * k - 1) : ℝ))
  linarith

end ConstructionData
end ThesisCommon.GowersMaurey
