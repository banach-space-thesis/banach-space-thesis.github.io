import ThesisCommon.Analysis.CZeroNormingBlocks

/-! An explicit c₀ nondistortion block construction from an actual lower
operator bound. The infimum of the tail norms supplies a common scale;
finite disjoint blocks approach it uniformly. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_cZero_almost_maximal_blocks_of_tail_lower_bound (V : CZeroSum 𝕜 →L[𝕜] E)
    {c δ : ℝ} (hc : 0 < c)
    (htail : ∀ n, c ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding n))‖)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ∃ b : ℝ,
      c ≤ b ∧ ‖A‖ ≤ 1 ∧ ‖V.comp A‖ ≤ b ∧
      ∀ n, (1-δ)*b < ‖V (A (cZeroSingle n 1))‖ := by
  classical
  let J (n : ℕ) := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding n)
  let f (n : ℕ) := ‖V.comp (J n)‖
  have hcf (n : ℕ) : c ≤ f n := htail n
  let b₀ := sInf (Set.range f)
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨n, rfl⟩; exact hcf n⟩
  have hcb₀ : c ≤ b₀ := le_csInf (Set.range_nonempty f) (by rintro _ ⟨n, rfl⟩; exact hcf n)
  have hb₀pos : 0 < b₀ := hc.trans_le hcb₀
  have hb₀f (n : ℕ) : b₀ ≤ f n := csInf_le hbdd ⟨n, rfl⟩
  have hbigger : b₀ < b₀/(1-δ) := by
    rw [lt_div_iff₀ (by linarith : 0 < 1-δ)]
    nlinarith
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f) hbigger
  let W := V.comp (J N)
  have hr : (1-δ)*f N < b₀ := by
    have h := (lt_div_iff₀ (by linarith : 0 < 1-δ)).1 hN
    nlinarith
  have htail (p : ℕ) : W.comp (cZeroExtend (cZeroTailEmbedding p)) = V.comp (J (N+p)) := by
    change (V.comp (cZeroExtend (cZeroTailEmbedding N))).comp
      (cZeroExtend (cZeroTailEmbedding p)) = _
    rw [ContinuousLinearMap.comp_assoc, cZeroExtend_comp]
    congr 1
    congr 1
    ext n
    simp [cZeroTailEmbedding, Nat.add_assoc]
  obtain ⟨A, hA, hcol⟩ := exists_cZero_norming_block_operator W
    (fun p => by rw [htail]; exact hr.trans_le (hb₀f (N+p)))
  refine ⟨(J N).comp A, f N, hcf N, ?_, ?_, hcol⟩
  · exact ((J N).opNorm_comp_le A).trans
      ((mul_le_mul (norm_cZeroExtend_le (cZeroTailEmbedding N)) hA
        (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
  · rw [← ContinuousLinearMap.comp_assoc]
    exact (W.opNorm_comp_le A).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hA (norm_nonneg W))

theorem exists_cZero_almost_maximal_tail_blocks (V : CZeroSum 𝕜 →L[𝕜] E)
    {c δ : ℝ} (hc : 0 < c) (hlower : ∀ x, c*‖x‖ ≤ ‖V x‖)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ∃ b : ℝ,
      c ≤ b ∧ ‖A‖ ≤ 1 ∧ ‖V.comp A‖ ≤ b ∧
      ∀ n, (1-δ)*b < ‖V (A (cZeroSingle n 1))‖ := by
  apply exists_cZero_almost_maximal_blocks_of_tail_lower_bound V hc _ hδ hδ1
  intro n
  let J := cZeroExtend (𝕜 := 𝕜) (X := 𝕜) (cZeroTailEmbedding n)
  have he : ‖cZeroSingle 0 (1 : 𝕜)‖ = 1 :=
    (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0
  have h := hlower (J (cZeroSingle 0 1))
  have hiso := scalarCZeroExtend_norm (𝕜 := 𝕜) (cZeroTailEmbedding n) (cZeroSingle 0 1)
  have hnorm := (V.comp J).le_opNorm (cZeroSingle 0 1)
  rw [show ‖J (cZeroSingle 0 1)‖ = 1 by exact hiso.trans he, mul_one] at h
  rw [he, mul_one] at hnorm
  exact h.trans hnorm

end ThesisCommon
