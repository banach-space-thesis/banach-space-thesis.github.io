import ThesisCommon.Analysis.LpOperatorFiniteCorners
import ThesisCommon.Analysis.SequencePrefixes
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Finite initial corners converge coordinatewise to the original bounded
operator; truncation converges in the actual finite-p norm. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpInitial_extend_restrict_eq_prefix (p : BanachExponent) (n : ℕ)
    (x : lp (fun _ : ℕ => 𝕜) p.val) :
    lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
      (lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x) = lpPrefix n x := by
  apply lp.ext
  funext k
  by_cases hk : k ≤ n
  · let i : Fin (n+1) := ⟨k, by omega⟩
    change lpExtend (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n)
      (lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x)
        (finiteLpInitialEmbedding n i) = if k ≤ n then x k else 0
    rw [lpExtend_apply_image, if_pos hk]
    rfl
  · have hnot : k ∉ Set.range (finiteLpInitialEmbedding n) := by
      rintro ⟨i, hi⟩
      change i.val = k at hi
      have := i.isLt
      omega
    change Function.extend (finiteLpInitialEmbedding n)
      (lpRestrict (𝕜 := 𝕜) p.val (finiteLpInitialEmbedding n) x) 0 k =
        if k ≤ n then x k else 0
    rw [Function.extend_apply' _ _ _ hnot, if_neg hk]
    rfl

theorem lpPrefix_tendsto (p : BanachExponent) (hp : p.val ≠ ∞)
    (x : lp (fun _ : ℕ => 𝕜) p.val) :
    Tendsto (fun n => lpPrefix n x) atTop (𝓝 x) := by
  simpa only [lpPrefix_eq_sum_single] using
    (lp.hasSum_single hp x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem finite_matrix_corners_coordinate_tendsto (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : ScalarLpOperator 𝕜 p) (x : lp (fun _ : ℕ => 𝕜) p.val) (k : ℕ) :
    Tendsto (fun n => finiteMatrixToLpOperator p n (lpOperatorToFiniteMatrix p n T) x k)
      atTop (𝓝 (T x k)) := by
  have hT := ((lpCoordinate (𝕜 := 𝕜) p.val k).continuous.tendsto (T x)).comp
    ((T.continuous.tendsto x).comp (lpPrefix_tendsto p hp x))
  apply hT.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  let i : Fin (n+1) := ⟨k, by omega⟩
  change T (lpPrefix n x) k =
    finiteMatrixToLpOperator p n (lpOperatorToFiniteMatrix p n T) x i.val
  rw [finiteMatrixToLpOperator_apply_image, lpOperatorToFiniteMatrix_apply,
    lpInitial_extend_restrict_eq_prefix]

end ThesisCommon

