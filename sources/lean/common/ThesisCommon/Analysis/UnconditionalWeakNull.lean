import ThesisCommon.Analysis.EllOneSubsequenceSpan

/-! The unconditional lower-estimate direction of PFP Lemma 3.1, with an
arbitrary unconditional constant and an actual ℓ₁ subsequence span. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem UnconditionalWith.subsequence_bound {K : ℝ} (hb : b.UnconditionalWith K)
    (f : ℕ ↪ ℕ) (F : Finset ℕ) (a c : ℕ → 𝕜)
    (hac : ∀ n ∈ F, ‖a n‖ ≤ ‖c n‖) :
    ‖∑ n ∈ F, a n • b.vector (f n)‖ ≤ K * ‖∑ n ∈ F, c n • b.vector (f n)‖ := by
  classical
  have h := hb.2 (F.map f) (fun n => a (Function.invFun f n))
    (fun n => c (Function.invFun f n)) (by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hn
      simpa only [Function.leftInverse_invFun f.injective i] using hac i hi)
  have heq (n : ℕ) : Function.invFun f (f n) = n := Function.leftInverse_invFun f.injective n
  simpa only [Finset.sum_map, heq] using h

theorem subsequence_lower_of_large_functional {K : ℝ} (hb : b.UnconditionalWith K)
    (φ : X →L[𝕜] 𝕜) (f : ℕ ↪ ℕ) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ n, ε ≤ ‖φ (b.vector (f n))‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Finset ℕ) (a : ℕ → 𝕜),
      c * ∑ n ∈ F, ‖a n‖ ≤ ‖∑ n ∈ F, a n • b.vector (f n)‖ := by
  have hK : 0 < K := zero_lt_one.trans_le hb.1
  have hn (n : ℕ) : φ (b.vector (f n)) ≠ 0 := norm_pos_iff.mp (hε.trans_le (hf n))
  have hφ : 0 < ‖φ‖ := by
    have hh := (hf 0).trans (φ.le_opNorm (b.vector (f 0)))
    rw [b.norm_vector, mul_one] at hh
    exact hε.trans_le hh
  refine ⟨ε / (‖φ‖ * K), div_pos hε (mul_pos hφ hK), ?_⟩
  intro F a
  let d : ℕ → 𝕜 := fun n => ((ε * ‖a n‖ : ℝ) : 𝕜) / φ (b.vector (f n))
  have hd (n : ℕ) : ‖d n‖ ≤ ‖a n‖ := by
    dsimp [d]
    rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg hε.le (norm_nonneg _))]
    apply (div_le_iff₀ (hε.trans_le (hf n))).mpr
    nlinarith [norm_nonneg (a n), hf n]
  have hnorm := hb.subsequence_bound b f F d a (fun n _ => hd n)
  have heval : φ (∑ n ∈ F, d n • b.vector (f n)) =
      ((ε * ∑ n ∈ F, ‖a n‖ : ℝ) : 𝕜) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    calc
      _ = ∑ n ∈ F, ((ε * ‖a n‖ : ℝ) : 𝕜) := by
        apply Finset.sum_congr rfl
        intro n _
        exact div_mul_cancel₀ _ (hn n)
      _ = _ := by rw [← RCLike.ofReal_sum, Finset.mul_sum]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos hφ hK)).mpr
  calc
    ε * ∑ n ∈ F, ‖a n‖ = ‖φ (∑ n ∈ F, d n • b.vector (f n))‖ := by
      rw [heval, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    _ ≤ ‖φ‖ * ‖∑ n ∈ F, d n • b.vector (f n)‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (K * ‖∑ n ∈ F, a n • b.vector (f n)‖) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := by ring

theorem weakly_null_of_no_ellOne_subsequence [CompleteSpace X] (hb : b.IsUnconditional)
    (hnot : ∀ f : ℕ → ℕ, StrictMono f →
      ¬ Nonempty (b.subsequenceSpan f ≃L[𝕜] lp (fun _ : ℕ => 𝕜) 1))
    (φ : X →L[𝕜] 𝕜) : Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  simp only [dist_zero_right]
  by_contra h
  push_neg at h
  have hfreq : ∃ᶠ n in atTop, ε ≤ ‖φ (b.vector n)‖ := Filter.frequently_atTop.mpr h
  obtain ⟨f, hf, hlarge⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨K, hK⟩ := hb
  obtain ⟨c, hc, hlower⟩ := b.subsequence_lower_of_large_functional hK φ
    ⟨f, hf.injective⟩ hε hlarge
  exact hnot f hf (b.subsequenceSpan_equiv_ellOne_of_lower f hc hlower)

end NormalizedSchauderBasis
end ThesisCommon
