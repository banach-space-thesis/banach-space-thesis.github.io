import ThesisCommon.Analysis.SubsymmetricBasis
import ThesisCommon.Analysis.UnconditionalOperatorBounds
import ThesisCommon.Analysis.SchauderSelection
import ThesisCommon.Analysis.Factorization

/-! The subsymmetric extension in PFP Remark 3.4, with the original norm
and explicit unconditional/subsequence constants. Increasing subsequence
operators are constructed, not assumed; the final correction is Neumann's. -/
noncomputable section
open Filter Topology
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] (b : NormalizedSchauderBasis 𝕜 X)

theorem subsymmetric_factors_of_large_diagonal {K C : ℝ}
    (hs : b.SubsymmetricWith K C)
    (hweak : ∀ φ : X →L[𝕜] 𝕜, Tendsto (fun n => φ (b.vector n)) atTop (𝓝 0))
    (T : X →L[𝕜] X) {M : Set ℕ} (hM : M.Infinite)
    (hlarge : ∀ n ∈ M, (1 / 2 : ℝ) ≤ ‖b.coord n (T (b.vector n))‖) :
    FactorsIdentityWith T X (4 * K ^ 2 * C ^ 2) := by
  have hK : 0 < K := zero_lt_one.trans_le hs.1.1
  have hC : 0 < C := zero_lt_one.trans_le hs.2.1
  let ε : ℝ := 1 / (8 * K * K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨f, hf, hmem, hsmall⟩ := b.small_off_diagonal_subsequence hweak T hM hε
  obtain ⟨A, B, hAB, hA, hB, hBe, hAc⟩ := b.exists_subsymmetric_compression hs f hf
  let S : X →L[𝕜] X := (A.comp T).comp B
  let d : ℕ → 𝕜 := fun n => b.coord n (S (b.vector n))
  have hd (n : ℕ) : ‖d n‖ ≤ K * ‖S‖ := by
    calc
      _ ≤ K * ‖S (b.vector n)‖ := hs.1.coord_le_bound b n _
      _ ≤ K * (‖S‖ * ‖b.vector n‖) := mul_le_mul_of_nonneg_left (S.le_opNorm _) hK.le
      _ = _ := by rw [b.norm_vector, mul_one]
  obtain ⟨D, _, hDe⟩ := hs.1.exists_diagonal_bound b d
    (mul_nonneg hK.le (norm_nonneg S)) hd
  have hdiag (n : ℕ) : d n = b.coord (f n) (T (b.vector (f n))) := by
    change b.coord n (A (T (B (b.vector n)))) = _
    rw [hBe, hAc]
  have hhalf (n : ℕ) : (1 / 2 : ℝ) ≤ ‖d n‖ := by
    rw [hdiag]
    exact hlarge (f n) (hmem n)
  have hn (n : ℕ) : d n ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hhalf n))
  have hinv (n : ℕ) : ‖(d n)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hhalf n))]
    linarith [hhalf n]
  obtain ⟨R, hR, hRe⟩ := hs.1.exists_diagonal_bound b (fun n => (d n)⁻¹)
    (by norm_num : (0 : ℝ) ≤ 2) hinv
  have hD : FactorsIdentityWith D X (2 * K) := by
    refine ⟨R, ContinuousLinearMap.id 𝕜 X, ?_, ?_⟩
    · apply b.operator_ext
      intro n
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hDe,
        map_smul, hRe, smul_smul, mul_inv_cancel₀ (hn n), one_smul]
    · calc
        _ ≤ (K * 2) * 1 := mul_le_mul hR ContinuousLinearMap.norm_id_le
          (norm_nonneg _) (by positivity)
        _ = _ := by ring
  have hnorm : ‖S - D‖ ≤ K * ε := by
    apply hs.1.norm_le_of_geometric_entries b _ hε.le
    intro i j
    simp only [ContinuousLinearMap.sub_apply, map_sub, hDe, map_smul,
      b.biorthogonal, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_one]
      change ‖d i - d i‖ ≤ _
      rw [sub_self, norm_zero]
      positivity
    · simp only [if_neg hij, mul_zero, sub_zero]
      change ‖b.coord i (A (T (B (b.vector j))))‖ ≤ _
      rw [hAc, hBe]
      exact (hsmall i j hij).le
  have hpert : (2 * K) * ‖S - D‖ < 1 / 2 := by
    calc
      _ ≤ (2 * K) * (K * ε) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 1 / 4 := by dsimp [ε]; field_simp; ring
      _ < _ := by norm_num
  have hout := (hD.perturb hpert).of_compression (T := T) A B
  apply hout.mono
  calc
    _ ≤ (2 * (2 * K)) * ((C * K) * C) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hA hB (norm_nonneg _) (mul_nonneg hC.le hK.le)) (by positivity)
    _ = _ := by ring

theorem hasCPFP_of_subsymmetric {K C : ℝ} (hs : b.SubsymmetricWith K C)
    (hnot : ¬ b.EquivalentEllOne) : HasCPFP 𝕜 X (4 * K ^ 2 * C ^ 2) := by
  intro T
  let M : Set ℕ := {n | (1 / 2 : ℝ) ≤ ‖b.coord n (T (b.vector n))‖}
  by_cases hM : M.Infinite
  · exact Or.inl (b.subsymmetric_factors_of_large_diagonal hs
      (b.weakly_null_of_subsymmetric hs hnot) T hM (fun _ hn => hn))
  · apply Or.inr
    apply b.subsymmetric_factors_of_large_diagonal hs
      (b.weakly_null_of_subsymmetric hs hnot) _ (Set.not_infinite.mp hM).infinite_compl
    intro n hn
    have hlt : ¬ (1 / 2 : ℝ) ≤ ‖b.coord n (T (b.vector n))‖ := hn
    have hsum := norm_add_le (b.coord n (T (b.vector n)))
      (1 - b.coord n (T (b.vector n)))
    rw [add_sub_cancel, norm_one] at hsum
    have hh : (1 / 2 : ℝ) ≤ ‖1 - b.coord n (T (b.vector n))‖ := by linarith
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub, b.biorthogonal, ite_true] using hh

theorem hasUPFP_of_subsymmetric (hs : b.IsSubsymmetric) (hnot : ¬ b.EquivalentEllOne) :
    HasUPFP 𝕜 X := by
  obtain ⟨K, C, hs⟩ := hs
  refine ⟨max 1 (4 * K ^ 2 * C ^ 2), le_max_left _ _, ?_⟩
  intro T
  exact (b.hasCPFP_of_subsymmetric hs hnot T).imp
    (fun h => h.mono (le_max_right _ _)) (fun h => h.mono (le_max_right _ _))

end ThesisCommon.NormalizedSchauderBasis
