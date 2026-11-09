import ThesisCommon.Analysis.SchauderSummablePerturbation
import ThesisCommon.Analysis.SchauderMatrix
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Geometric off-diagonal errors give a bounded diagonal perturbation
on any normalized Schauder basis with bounded coordinate functionals.
No unconditionality assumption is used. -/

noncomputable section
open scoped BigOperators
namespace ThesisCommon.NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem hasSum_geometric_matrix {c : ℝ} (hc : 0 ≤ c) :
    HasSum (fun ij : ℕ × ℕ => c * (1 / 2 : ℝ) ^ (ij.1 + ij.2 + 2)) c := by
  have h1 := hasSum_half_geometric.mul_left c
  have h2 := hasSum_half_geometric
  have hs := h1.summable.mul_of_nonneg h2.summable
    (fun j => by positivity) (fun j => by positivity)
  convert h1.mul h2 hs using 1
  · funext ij
    simp only [pow_add, pow_two]
    ring
  · ring

theorem exists_diagonal_of_geometric_entries (b : NormalizedSchauderBasis 𝕜 X)
    {K c : ℝ} (hK : ∀ n, ‖b.coord n‖ ≤ K) (hc : 0 ≤ c)
    (S : X →L[𝕜] X)
    (hS : ∀ i j, i ≠ j → ‖b.coord i (S (b.vector j))‖ ≤ c * (1 / 2 : ℝ) ^ (i + j + 2)) :
    ∃ D : X →L[𝕜] X, ‖S - D‖ ≤ K * c ∧
      ∀ j, D (b.vector j) = b.coord j (S (b.vector j)) • b.vector j := by
  let a : ℕ × ℕ → 𝕜 := fun ij => if ij.1 = ij.2 then 0 else b.coord ij.1 (S (b.vector ij.2))
  have hbound (ij : ℕ × ℕ) : ‖a ij‖ ≤ c * (1 / 2 : ℝ) ^ (ij.1 + ij.2 + 2) := by
    dsimp only [a]
    split_ifs with hij
    · simp only [norm_zero]
      positivity
    · exact hS _ _ hij
  have hmajor := hasSum_geometric_matrix hc
  have ha : Summable (fun ij => ‖a ij‖) :=
    hmajor.summable.of_nonneg_of_le (fun ij => norm_nonneg _) hbound
  have hsum : (∑' ij, ‖a ij‖) ≤ c :=
    (ha.tsum_le_tsum hbound hmajor.summable).trans_eq hmajor.tsum_eq
  have hK0 : 0 ≤ K := (norm_nonneg (b.coord 0)).trans (hK 0)
  refine ⟨S - b.summableMatrix a, ?_, b.subtract_offDiagonal_action hK S ha⟩
  rw [sub_sub_cancel]
  exact (b.norm_summableMatrix_le hK a ha).trans (mul_le_mul_of_nonneg_left hsum hK0)

end ThesisCommon.NormalizedSchauderBasis
