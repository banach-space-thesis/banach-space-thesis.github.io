import SurveyStatements.P5OperatorReductionCanonicalBudgets
import SurveyStatements.P5GeneralMixedErrorOperators

/-! Actual vector and reader norms are paid for before the tree selection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal BigOperators Classical
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support
attribute [local irreducible] probabilityLpIntegral probabilityLpMean
  outerExpectation innerExpectation DoublyZeroMean

def outerNormWeight (𝕜 : Type*) [RCLike 𝕜] (q : ℕ × ℕ) : ℝ :=
  4 * (‖dyadicHaar 𝕜 1 (BiTree.heapDecode q.1)‖ *
    (14 * ‖dyadicHaarCoordinate 𝕜 1 (BiTree.heapDecode q.2)‖))

def innerNormWeight (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (q : ℕ × ℕ) : ℝ :=
  4 * (‖dyadicHaar 𝕜 p.val (BiTree.heapDecode q.1)‖ *
    (14 * (intervalLpDyadicRadius (BiTree.heapDecode q.2).1)⁻¹))

def mixedNormWeight (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ‖cancellativeHaarCoordinate 𝕜 p.val (BiTree.heapDecode q.2.1) (BiTree.heapDecode q.2.2)‖ *
    ‖cancellativeHaar 𝕜 p.val (BiTree.heapDecode q.1.1) (BiTree.heapDecode q.1.2)‖

structure ConcreteNormBudgets (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (ε : ℝ) where
  δo : ℕ → ℕ → ℝ
  δi : ℕ → ℕ → ℝ
  ν : ℕ → ℕ → ℕ → ℕ → ℝ
  δo_pos : ∀ i j, 0 < δo i j
  δi_pos : ∀ i j, 0 < δi i j
  ν_pos : ∀ i j k l, 0 < ν i j k l
  bo : GeneralMixedStripIndex → ℝ
  bi : GeneralMixedStripIndex → ℝ
  bm : GeneralMixedNuclearIndex → ℝ
  bo_sum : Summable bo
  bi_sum : Summable bi
  bm_sum : Summable bm
  bo_total : (∑' q, bo q) ≤ ε / 6
  bi_total : (∑' q, bi q) ≤ ε / 6
  bm_total : (∑' q, bm q) ≤ ε / 6
  outer_factor : ∀ q : GeneralMixedStripIndex,
    4 * (‖dyadicHaar 𝕜 1 q.val.1‖ *
      ((14 * δo (stripHeapIndices q).1 (stripHeapIndices q).2) *
        ‖dyadicHaarCoordinate 𝕜 1 q.val.2‖)) ≤ bo q
  inner_factor : ∀ q : GeneralMixedStripIndex,
    4 * (‖dyadicHaar 𝕜 p.val q.val.1‖ *
      ((14 * δi (stripHeapIndices q).1 (stripHeapIndices q).2) *
        (intervalLpDyadicRadius q.val.2.1)⁻¹)) ≤ bi q
  mixed_factor : ∀ q : GeneralMixedNuclearIndex,
    ν (nuclearHeapIndices q).1.1 (nuclearHeapIndices q).1.2
      (nuclearHeapIndices q).2.1 (nuclearHeapIndices q).2.2 *
        (‖cancellativeHaarCoordinate 𝕜 p.val q.val.2.1 q.val.2.2‖ *
          ‖cancellativeHaar 𝕜 p.val q.val.1.1 q.val.1.2‖) ≤ bm q

theorem exists_concrete_norm_budgets (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (ConcreteNormBudgets 𝕜 p ε) := by
  letI : Fact (1 ≤ p.val) := ⟨p.property⟩
  letI : NormedSpace 𝕜 (DoublyZeroMean 𝕜 p.val) := inferInstance
  have he : 0 < ε / 3 := div_pos hε (by norm_num)
  have ho : ∀ q, 0 ≤ outerNormWeight 𝕜 q := by
    intro q
    exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _)))
  have hi : ∀ q, 0 ≤ innerNormWeight 𝕜 p q := by
    intro q
    unfold innerNormWeight
    exact mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _)
      (mul_nonneg (by norm_num) (inv_nonneg.mpr (intervalLpDyadicRadius_pos _).le)))
  have hm : ∀ q, 0 ≤ mixedNormWeight 𝕜 p q := by
    intro q
    unfold mixedNormWeight
    exact mul_nonneg
      (ContinuousLinearMap.opNorm_nonneg (cancellativeHaarCoordinate 𝕜 p.val
        (BiTree.heapDecode q.2.1) (BiTree.heapDecode q.2.2)))
      (norm_nonneg (cancellativeHaar 𝕜 p.val
        (BiTree.heapDecode q.1.1) (BiTree.heapDecode q.1.2)))
  obtain ⟨do', hdo, hso, hto⟩ := exists_positive_reindexed_error_budget
    (outerNormWeight 𝕜) ho he stripHeapIndices stripHeapIndices_injective
  obtain ⟨di', hdi, hsi, hti⟩ := exists_positive_reindexed_error_budget
    (innerNormWeight 𝕜 p) hi he stripHeapIndices stripHeapIndices_injective
  obtain ⟨v', hv, hsm, htm⟩ := exists_positive_reindexed_error_budget
    (mixedNormWeight 𝕜 p) hm he nuclearHeapIndices nuclearHeapIndices_injective
  refine ⟨{
    δo := fun i j => do' (i, j)
    δi := fun i j => di' (i, j)
    ν := fun i j k l => v' ((i, j), (k, l))
    δo_pos := fun i j => hdo (i, j)
    δi_pos := fun i j => hdi (i, j)
    ν_pos := fun i j k l => hv ((i, j), (k, l))
    bo := fun q => outerNormWeight 𝕜 (stripHeapIndices q) * do' (stripHeapIndices q)
    bi := fun q => innerNormWeight 𝕜 p (stripHeapIndices q) * di' (stripHeapIndices q)
    bm := fun q => mixedNormWeight 𝕜 p (nuclearHeapIndices q) * v' (nuclearHeapIndices q)
    bo_sum := hso
    bi_sum := hsi
    bm_sum := hsm
    bo_total := hto.trans_eq (by ring)
    bi_total := hti.trans_eq (by ring)
    bm_total := htm.trans_eq (by ring)
    outer_factor := ?_
    inner_factor := ?_
    mixed_factor := ?_ }⟩
  · intro q
    dsimp only [outerNormWeight, stripHeapIndices]
    rw [BiTree.heapDecode_index, BiTree.heapDecode_index]
    apply le_of_eq
    ring
  · intro q
    dsimp only [innerNormWeight, stripHeapIndices]
    rw [BiTree.heapDecode_index, BiTree.heapDecode_index]
    apply le_of_eq
    ring
  · intro q
    dsimp only [mixedNormWeight, nuclearHeapIndices]
    rw [BiTree.heapDecode_index, BiTree.heapDecode_index,
      BiTree.heapDecode_index, BiTree.heapDecode_index]
    apply le_of_eq
    ring

end SurveyStatements.P5OperatorReduction
