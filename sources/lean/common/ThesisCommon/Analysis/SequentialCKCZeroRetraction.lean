import ThesisCommon.Analysis.SequentialCKNearRetraction
import ThesisCommon.Analysis.CZeroAlmostIsometricBlocks

/-! Quantitative complemented c₀ subcopies in C(K) for sequentially compact
K. Both the near-isometric blocks and their retraction are constructed from
the supplied operator lower bound. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [SeqCompactSpace K]

theorem exists_cZero_quantitative_retraction_of_sequentiallyCompact
    [Nonempty K] (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜))
    {c δ : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖V x‖)
    (hδ : 0 < δ) (hδsmall : 2*δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      ∃ R : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜,
        R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1-2*δ)⁻¹/c ∧
        ‖V.comp A‖ * ‖R‖ ≤ (1-2*δ)⁻¹ := by
  letI : NormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] C(K, 𝕜)) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] C(K, 𝕜)) _ _ _
  letI : NormSMulClass 𝕜 (C(K, 𝕜) →L[𝕜] CZeroSum 𝕜) :=
    @NormedSpace.toNormSMulClass 𝕜 (C(K, 𝕜) →L[𝕜] CZeroSum 𝕜) _ _ _
  obtain ⟨B, b, hcb, hB, hVB, hcol⟩ := exists_cZero_almost_maximal_tail_blocks
    V hc hlower hδ (by linarith)
  have hb : 0 < b := hc.trans_le hcb
  let U : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜) := ((b⁻¹ : ℝ) : 𝕜) • (V.comp B)
  have hU : ‖U‖ ≤ 1 := by
    dsimp [U]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    exact (mul_le_mul_of_nonneg_left hVB (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')
  have hUc (n : ℕ) : 1-δ ≤ ‖U (cZeroSingle n 1)‖ := by
    change 1-δ ≤ ‖((b⁻¹ : ℝ) : 𝕜) • V (B (cZeroSingle n 1))‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    have h := mul_le_mul_of_nonneg_left (hcol n).le (inv_nonneg.mpr hb.le)
    have heq : b⁻¹ * ((1-δ)*b) = 1-δ := by field_simp
    exact heq.symm.trans_le h
  obtain ⟨C, Q, hQC, hC, hQ⟩ := exists_cZero_retraction_of_near_unit_columns
    U hU hδ.le hδsmall hUc
  let A := B.comp C
  let R : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜 := ((b⁻¹ : ℝ) : 𝕜) • Q
  have hR : ‖R‖ ≤ b⁻¹*(1-2*δ)⁻¹ := by
    dsimp [R]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    exact mul_le_mul_of_nonneg_left hQ (inv_nonneg.mpr hb.le)
  have hVA : ‖V.comp A‖ ≤ b := by
    change ‖V.comp (B.comp C)‖ ≤ b
    rw [← ContinuousLinearMap.comp_assoc]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hVB hC (norm_nonneg C) hb.le).trans_eq (mul_one b))
  refine ⟨A, R, ?_, ?_, ?_, ?_⟩
  · simpa only [R, U, A, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul] using hQC
  · exact (B.opNorm_comp_le C).trans
      ((mul_le_mul hB hC (norm_nonneg C) zero_le_one).trans_eq (one_mul 1))
  · apply hR.trans
    rw [div_eq_mul_inv, mul_comm b⁻¹]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hc hcb)
      (inv_nonneg.mpr (by linarith))
  · apply (mul_le_mul hVA hR (norm_nonneg R) hb.le).trans_eq
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]

theorem exists_cZero_almost_contractive_projection_factors
    (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜))
    {c ε : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖V x‖) (hε : 0 < ε) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      ∃ R : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜,
        R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1+ε)/c ∧ ‖V.comp A‖*‖R‖ ≤ 1+ε := by
  classical
  have hne : Nonempty K := by
    by_contra hn
    have hz : V (cZeroSingle 0 1) = 0 := by ext t; exact (hn ⟨t⟩).elim
    have h := hlower (cZeroSingle 0 1)
    have he : ‖cZeroSingle 0 (1 : 𝕜)‖ = 1 := (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0
    rw [hz, norm_zero, he, mul_one] at h
    exact hc.not_ge h
  letI := hne
  let δ := ε/(2*(1+ε))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hdone : 2*δ < 1 := by
    dsimp [δ]
    have hh : 0 < 2*(1+ε) := by positivity
    have h := (div_lt_iff₀ hh).2 (by linarith : 2*ε < 1*(2*(1+ε)))
    simpa only [mul_div_assoc] using h
  have heq : (1-2*δ)⁻¹ = 1+ε := by
    dsimp [δ]
    have he : 1+ε ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  obtain ⟨A, R, hRA, hA, hR, hprod⟩ :=
    exists_cZero_quantitative_retraction_of_sequentiallyCompact V hc hlower hd hdone
  exact ⟨A, R, hRA, hA, by simpa only [heq] using hR, by simpa only [heq] using hprod⟩

theorem exists_cZero_subcopy_projection_of_sequentiallyCompact
    (V : CZeroSum 𝕜 →L[𝕜] C(K, 𝕜))
    {c ε : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖V x‖) (hε : 0 < ε) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜,
      ∃ R : C(K, 𝕜) →L[𝕜] CZeroSum 𝕜,
      ∃ P : C(K, 𝕜) →L[𝕜] C(K, 𝕜),
        R.comp (V.comp A) = ContinuousLinearMap.id 𝕜 (CZeroSum 𝕜) ∧
        ‖A‖ ≤ 1 ∧ ‖R‖ ≤ (1+ε)/c ∧ ‖V.comp A‖*‖R‖ ≤ 1+ε ∧
        P.comp P = P ∧ ‖P‖ ≤ 1+ε ∧
        Set.range P = Set.range (V.comp A) ∧ Set.range P ⊆ Set.range V := by
  obtain ⟨A, R, heq, hA, hR, hprod⟩ :=
    exists_cZero_almost_contractive_projection_factors V hc hlower hε
  let J := V.comp A
  let P := J.comp R
  have hRJ (x : CZeroSum 𝕜) : R (J x) = x := DFunLike.congr_fun heq x
  refine ⟨A, R, P, heq, hA, hR, hprod, ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    change J (R (J (R f))) = J (R f)
    rw [hRJ]
  · exact (J.opNorm_comp_le R).trans hprod
  · apply Set.Subset.antisymm
    · rintro _ ⟨f, rfl⟩
      exact ⟨R f, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨J x, by change J (R (J x)) = J x; rw [hRJ]⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨A (R f), rfl⟩

end ThesisCommon
