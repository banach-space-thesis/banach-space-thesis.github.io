import ThesisCommon.Analysis.MatrixSubsequenceCopy

/-! Norm-one insertion and retraction for the full subsequence coordinate
subspace, with the inherited norm and actual matrix block maps. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

local instance matrixSupportNormedSpace (p : BanachExponent) (I : Set ℕ) :
    NormedSpace 𝕜 (matrixSumSupport (𝕜 := 𝕜) p I) :=
  Submodule.normedSpace (𝕜 := 𝕜) (matrixSumSupport (𝕜 := 𝕜) p I)

theorem matrixSubsequenceCopy (p : BanachExponent) (n : ℕ → ℕ)
    (hinj : Function.Injective n) (hn : ∀ i, i ≤ n i) :
    ∃ (E : FiniteMatrixSum 𝕜 p →L[𝕜] matrixSumSupport (𝕜 := 𝕜) p (Set.range n))
      (P : matrixSumSupport (𝕜 := 𝕜) p (Set.range n) →L[𝕜] FiniteMatrixSum 𝕜 p),
      ‖E‖ = 1 ∧ ‖P‖ = 1 ∧ P.comp E = ContinuousLinearMap.id 𝕜 _ := by
  let M := matrixSumSupport (𝕜 := 𝕜) p (Set.range n)
  let E : FiniteMatrixSum 𝕜 p →L[𝕜] M :=
    (matrixSubsequenceInsert p n hn).codRestrict M (matrixSubsequenceInsert_support p n hn)
  let P : M →L[𝕜] FiniteMatrixSum 𝕜 p :=
    (matrixSubsequenceRead p n hn).comp M.subtypeL
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound E zero_le_one
    intro x
    change ‖matrixSubsequenceInsert p n hn x‖ ≤ 1 * ‖x‖
    exact ((matrixSubsequenceInsert (𝕜 := 𝕜) p n hn).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_matrixSubsequenceInsert_le (𝕜 := 𝕜) p n hn) (norm_nonneg x))
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound P zero_le_one
    intro x
    change ‖matrixSubsequenceRead p n hn x.val‖ ≤ 1 * ‖x.val‖
    exact ((matrixSubsequenceRead (𝕜 := 𝕜) p n hn).le_opNorm x.val).trans
      (mul_le_mul_of_nonneg_right (norm_matrixSubsequenceRead_le (𝕜 := 𝕜) p n hn) (norm_nonneg x.val))
  have hPE : P.comp E = ContinuousLinearMap.id 𝕜 _ :=
    matrixSubsequenceRead_comp_insert p n hinj hn
  let x : FiniteMatrixSum 𝕜 p := lp.single ∞ 0
    (matrixUnit (𝕜 := 𝕜) p (0 : Fin 1) (0 : Fin 1))
  have hx : ‖x‖ = 1 := by
    dsimp only [x]
    rw [lp.norm_single (by simp), norm_matrixUnit]
  have hPx : P (E x) = x := DFunLike.congr_fun hPE x
  have hprod : 1 ≤ ‖P‖ * ‖E‖ := by
    have ha := P.le_opNorm (E x)
    rw [hPx, hx] at ha
    have hb := mul_le_mul_of_nonneg_left (E.le_opNorm x) (norm_nonneg P)
    rw [hx, mul_one] at hb
    exact ha.trans hb
  refine ⟨E, P, ?_, ?_, hPE⟩
  · apply le_antisymm hE
    simpa only [one_mul] using hprod.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg E))
  · apply le_antisymm hP
    simpa only [mul_one] using hprod.trans (mul_le_mul_of_nonneg_left hE (norm_nonneg P))

end ThesisCommon
