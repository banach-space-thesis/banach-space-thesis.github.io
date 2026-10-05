import ThesisCommon.Analysis.UncountableSchauderOperators
import ThesisCommon.Analysis.UncountableSchauderSumSupport

/-! Actual coordinate compression and insertion for arbitrary-index symmetric
vector sums. Finite permutation symmetry constructs scalar maps; their exact
coordinates realize the required vector norm sequences. -/
noncomputable section
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜] [Nonempty Γ]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E}

theorem exists_reindexed_compression (hs : b.HasSymmetricNorm) (f : Γ ↪ Γ) :
    ∃ A B : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ x i, A x i = x (f i)) ∧
      (∀ x j, B x j = if h : j ∈ Set.range f then x h.choose else 0) ∧
      ∀ x, ‖B x‖ = ‖x‖ := by
  classical
  obtain ⟨a, c, hac, ha, hc, hce, hacoord⟩ := b.exists_subsequence_compression hs f
  have hccoord := b.coord_insertion f c hce
  let A₀ : UncountableSchauderSum b hs.1 X →ₗ[𝕜] UncountableSchauderSum b hs.1 X :=
    { toFun := fun x => ⟨fun i => x (f i), ⟨a (normVector x), by
        intro i
        rw [hacoord, coord_normVector]⟩⟩
      map_add' := fun x y => by ext i; rfl
      map_smul' := fun r x => by ext i; rfl }
  have hAnorm (x : UncountableSchauderSum b hs.1 X) : ‖A₀ x‖ ≤ 1 * ‖x‖ := by
    have hn : normVector (A₀ x) = a (normVector x) := by
      apply normVector_eq
      intro i
      rw [hacoord, coord_normVector]
      rfl
    change ‖normVector (A₀ x)‖ ≤ 1 * ‖normVector x‖
    rw [hn]
    exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  let B₀ : UncountableSchauderSum b hs.1 X →ₗ[𝕜] UncountableSchauderSum b hs.1 X :=
    { toFun := fun x => ⟨fun j => if h : j ∈ Set.range f then x h.choose else 0,
        ⟨c (normVector x), by
          intro j
          rw [hccoord]
          by_cases h : j ∈ Set.range f <;> simp [h]⟩⟩
      map_add' := fun x y => by
        ext j
        change (if h : j ∈ Set.range f then (x + y) h.choose else 0) =
          (if h : j ∈ Set.range f then x h.choose else 0) +
          (if h : j ∈ Set.range f then y h.choose else 0)
        by_cases h : j ∈ Set.range f
        · simp only [dif_pos h, add_apply]
        · simp only [dif_neg h, add_zero]
      map_smul' := fun r x => by
        ext j
        change (if h : j ∈ Set.range f then (r • x) h.choose else 0) =
          r • (if h : j ∈ Set.range f then x h.choose else 0)
        by_cases h : j ∈ Set.range f
        · simp only [dif_pos h, smul_apply]
        · simp only [dif_neg h, smul_zero] }
  have hBnorm (x : UncountableSchauderSum b hs.1 X) : ‖B₀ x‖ ≤ 1 * ‖x‖ := by
    have hn : normVector (B₀ x) = c (normVector x) := by
      apply normVector_eq
      intro j
      rw [hccoord]
      change (if h : j ∈ Set.range f then b.coord h.choose (normVector x) else 0) =
        (‖if h : j ∈ Set.range f then x h.choose else 0‖ : 𝕜)
      split_ifs <;> simp only [coord_normVector, norm_zero, RCLike.ofReal_zero]
    change ‖normVector (B₀ x)‖ ≤ 1 * ‖normVector x‖
    rw [hn]
    exact (c.le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  let A := A₀.mkContinuous 1 hAnorm
  let B := B₀.mkContinuous 1 hBnorm
  have hA : ‖A‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hB : ‖B‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 _ := by
    ext x i
    change (if h : f i ∈ Set.range f then x h.choose else 0) = x i
    rw [dif_pos (Set.mem_range_self i)]
    exact congrArg (fun j => x j) (f.injective (Set.mem_range_self i).choose_spec)
  refine ⟨A, B, hAB, hA, hB, (fun _ _ => rfl), (fun _ _ => rfl), ?_⟩
  intro x
  apply le_antisymm
  · simpa only [one_mul] using hBnorm x
  · have he : A (B x) = x := DFunLike.congr_fun hAB x
    calc
      ‖x‖ = ‖A (B x)‖ := congrArg norm he.symm
      _ ≤ ‖B x‖ := by simpa only [one_mul] using hAnorm (B x)

end UncountableSchauderSum
end ThesisCommon
