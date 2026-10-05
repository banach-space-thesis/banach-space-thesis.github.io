import ThesisCommon.Analysis.GowersMaureyNPairs

/-! The two numerical N-pair bounds used in source Lemma 8.
For an actual odd construction size N, every integer interval order
between one and sqrt N gives interval norm at most eight. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_square_le {x : ℝ} (hx : 0 ≤ x) :
    logarithmicWeight (x^2) ≤ 2 * logarithmicWeight x := by
  have hlog := Real.log_le_log (by positivity : 0 < x^2+1)
    (show x^2+1 ≤ (x+1)^2 by nlinarith)
  rw [Real.log_pow] at hlog
  unfold logarithmicWeight
  calc
    _ ≤ (2 * Real.log (x+1)) / Real.log 2 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlog) (Real.log_nonneg (by norm_num))
    _ = _ := by ring

theorem log_le_sqrt_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (div_pos hs (by norm_num : (0:ℝ)<2))
  rw [Real.log_div hs.ne' (by norm_num : (2:ℝ) ≠ 0), Real.log_sqrt hx.le] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith

theorem normalizedPairSize_bounds {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (hnN : (n : ℝ) ≤ Real.sqrt N) :
    (N : ℝ)/n ∈ Set.Icc (Real.log N) (Real.exp N) ∧
      logarithmicWeight N ≤ 2*logarithmicWeight ((N : ℝ)/n) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN1
  have hs : Real.sqrt (N : ℝ) ≤ (N : ℝ)/n := by
    apply (le_div_iff₀ hnr).mpr
    nlinarith [Real.sq_sqrt hNr.le, Real.sqrt_nonneg (N : ℝ)]
  have hu : (N : ℝ)/n ≤ N := (div_le_self hNr.le hn1)
  refine ⟨⟨(log_le_sqrt_of_pos hNr).trans hs,
    hu.trans ((show (N : ℝ) ≤ (N : ℝ)+1 by linarith).trans (Real.add_one_le_exp _))⟩, ?_⟩
  calc
    logarithmicWeight N = logarithmicWeight ((Real.sqrt (N : ℝ))^2) := by rw [Real.sq_sqrt hNr.le]
    _ ≤ 2*logarithmicWeight (Real.sqrt (N : ℝ)) := logarithmicWeight_square_le (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (logarithmicWeight_strictMonoOn.monotoneOn hs1 (hs1.trans hs) hs) (by norm_num)

theorem normalizedPairVector_intervalNorm_le_eight {𝕜 : Type*} [RCLike 𝕜]
    {D : ConstructionData 𝕜} (m : ℕ) {u : Fin (D.j (2*m+1)) → C00 𝕜}
    (h : IsRIS D 1 u) {n : ℕ} (hn : 0 < n)
    (hnN : (n : ℝ) ≤ Real.sqrt (D.j (2*m+1) : ℝ)) :
    intervalNorm D n (normalizedPairVector u) ≤ 8 := by
  obtain ⟨hgap,hweight⟩ := normalizedPairSize_bounds (D.j_positive _) hn hnN
  have hb := h.normalized_intervalNorm_le_lemma7 m n hgap
    (δ := 1) (by norm_num) (by simpa only [one_add_one_eq_two] using hweight)
  norm_num at hb
  exact hb

end ThesisCommon.GowersMaurey
