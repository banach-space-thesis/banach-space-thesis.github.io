import ThesisCommon.Analysis.BoundedEquivalenceCalculus

/-! Actual c₀ estimates for the quantitative sequence decomposition. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem cZero_norm_le_mul_of_pointwise (x : CZeroSum X) (y : CZeroSum Y)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖y i‖ ≤ C * ‖x i‖) : ‖y‖ ≤ C * ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg x))).mpr
  intro i
  exact (h i).trans (mul_le_mul_of_nonneg_left
    (BoundedContinuousFunction.norm_coe_le_norm x.toBCF i) hC)

theorem EquivNormBound.cZeroMap {e : X ≃L[𝕜] Y} {C : ℝ}
    (h : EquivNormBound e C) (hC : 0 ≤ C) :
    EquivNormBound (cZeroMapEquiv (ι := ℕ) e) C := by
  constructor
  · intro x
    exact cZero_norm_le_mul_of_pointwise x _ hC (fun i => h.1 (x i))
  · intro y
    exact cZero_norm_le_mul_of_pointwise y _ hC (fun i => h.2 (y i))

theorem equivNormBound_cZeroProd :
    EquivNormBound (cZeroProdEquiv (𝕜 := 𝕜) (ι := ℕ) (X := X) (Y := Y)) 2 := by
  have h : EquivNormBound (cZeroProdEquiv (𝕜 := 𝕜) (ι := ℕ) (X := X) (Y := Y)) 1 := by
    constructor
    · intro x
      apply max_le
      · exact cZero_norm_le_mul_of_pointwise x _ zero_le_one
          (fun i => by simpa using norm_fst_le (x i))
      · exact cZero_norm_le_mul_of_pointwise x _ zero_le_one
          (fun i => by simpa using norm_snd_le (x i))
    · intro x
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
      intro i
      change ‖(x.1 i, (0 : Y)) + ((0 : X), x.2 i)‖ ≤ ‖x‖
      simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.norm_def]
      exact max_le
        ((BoundedContinuousFunction.norm_coe_le_norm x.1.toBCF i).trans (norm_fst_le x))
        ((BoundedContinuousFunction.norm_coe_le_norm x.2.toBCF i).trans (norm_snd_le x))
  exact h.mono (by norm_num)

theorem equivNormBound_cZeroHeadTail :
    EquivNormBound (cZeroHeadTailEquiv (𝕜 := 𝕜) (X := X)) 2 := by
  constructor
  · intro x
    apply max_le
    · change ‖x 0‖ ≤ 2 * ‖x‖
      have h := BoundedContinuousFunction.norm_coe_le_norm x.toBCF 0
      change ‖x 0‖ ≤ ‖x‖ at h
      nlinarith [norm_nonneg x]
    · change ‖cZeroRestrict (𝕜 := 𝕜) sequenceSuccessor x‖ ≤ 2 * ‖x‖
      have h := norm_cZeroRead_le sequenceSuccessor x
      change ‖cZeroRestrict (𝕜 := 𝕜) sequenceSuccessor x‖ ≤ ‖x‖ at h
      nlinarith [norm_nonneg x]
  · intro x
    have h₁ := norm_cZeroSingle_le 0 x.1
    have h₂ : ‖cZeroExtend (𝕜 := 𝕜) sequenceSuccessor x.2‖ ≤ ‖x.2‖ := by
      have h := (cZeroExtend (𝕜 := 𝕜) (X := X) sequenceSuccessor).le_of_opNorm_le
        (norm_cZeroExtend_le (𝕜 := 𝕜) (X := X) sequenceSuccessor) x.2
      simpa only [one_mul] using h
    change ‖cZeroSingle 0 x.1 + cZeroExtend (𝕜 := 𝕜) sequenceSuccessor x.2‖ ≤ 2 * ‖x‖
    exact (norm_add_le _ _).trans (by nlinarith [norm_fst_le x, norm_snd_le x])

end ThesisCommon
