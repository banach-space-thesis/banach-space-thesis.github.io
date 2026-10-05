import ThesisCommon.Analysis.GowersMaureyMismatchSizes

/-! Explicit budgets for the low coding sizes in the special-functional
comparison. Only the rapid sequence and its first-size bound are used;
no growth assumption on the injective coding map is introduced. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ConstructionData.special_weight_low_code_budget
    (D : ConstructionData 𝕜) (t : ℕ) :
    (4 * ((t : ℝ) + 3)) ^ 2 ≤ logarithmicWeight (D.j (2 * t)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h := D.first_large
    norm_num at *
    linarith
  · have hj0 : 3 ≤ D.j 0 := by
      have h := D.size_large 0
      exact_mod_cast (show (3 : ℝ) ≤ D.j 0 by linarith)
    have hnat : t + 3 ≤ D.j t := by
      have h := D.j_strict.add_le_nat t 0
      simp only [Nat.add_zero] at h
      omega
    have hprev : (t : ℝ) + 3 ≤ D.j t := by exact_mod_cast hnat
    have hlarge : 64 ≤ (D.j t : ℝ) := by
      have h := D.size_large t
      linarith
    have hsq : (4 * ((t : ℝ) + 3)) ^ 2 ≤
        16 * ((D.j t : ℝ) + 1) ^ 2 := by
      have hp : 0 ≤ (t : ℝ) + 3 := by positivity
      have hh := pow_le_pow_left₀ hp (show (t : ℝ) + 3 ≤ (D.j t : ℝ) + 1 by linarith) 2
      nlinarith
    have hlog : 0 ≤ Real.log (D.j (2 * t) : ℝ) :=
      Real.log_nonneg (D.one_le_size _)
    calc
      _ ≤ 16 * ((D.j t : ℝ) + 1) ^ 2 := hsq
      _ ≤ Real.exp (D.j t : ℝ) := exp_ge_sixteen_add_one_sq hlarge
      _ ≤ Real.exp (2 * (D.j t : ℝ)) := Real.exp_le_exp.mpr (by linarith [D.one_le_size t])
      _ ≤ Real.log (Real.log (D.j (2 * t) : ℝ)) :=
        (D.exp_twice_size_lt_loglog (by omega : t < 2 * t)).le
      _ ≤ Real.log (D.j (2 * t) : ℝ) := Real.log_le_self hlog
      _ ≤ logarithmicWeight (D.j (2 * t)) := log_le_logarithmicWeight (D.one_le_size _)

theorem ConstructionData.low_code_count_div_sqrt_weight_le
    (D : ConstructionData 𝕜) (t : ℕ) :
    ((t : ℝ) + 3) / Real.sqrt (logarithmicWeight (D.j (2 * t))) ≤ 1 / 4 := by
  have hweight := D.specialSize_weight_large ⟨t, rfl⟩
  have hpos : 0 < Real.sqrt (logarithmicWeight (D.j (2 * t))) :=
    Real.sqrt_pos.mpr (by linarith)
  have h := Real.le_sqrt_of_sq_le (D.special_weight_low_code_budget t)
  apply (div_le_iff₀ hpos).mpr
  linarith

end ThesisCommon.GowersMaurey
