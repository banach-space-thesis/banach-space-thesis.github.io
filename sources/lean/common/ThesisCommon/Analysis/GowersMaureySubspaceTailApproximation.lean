import ThesisCommon.Analysis.FiniteCoordinateKernel
import ThesisCommon.Analysis.GowersMaureySchauderBasis
import ThesisCommon.Analysis.GowersMaureyBlockTails

/-! Every infinite-dimensional subspace of the actual completed space
has unit vectors in each finite-coordinate kernel. Genuine initial
truncations approximate them by finite vectors beyond the same cutoff.
No exact finite-support vector in the original subspace is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def initialCoefficients (D : ConstructionData 𝕜) (N : ℕ) (x : ShiftSpace D) : C00 𝕜 :=
  ∑ j ∈ Finset.range N, Finsupp.single j (completedCoordinate D j x)

theorem denseEmbedding_initialCoefficients (D : ConstructionData 𝕜) (N : ℕ)
    (x : ShiftSpace D) : denseEmbedding D (initialCoefficients D N x) = initialSum D N x := by
  rw [initialCoefficients, map_sum, initialSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [basisVector, ← map_smul]
  apply congrArg (denseEmbedding D)
  change (Finsupp.single j (completedCoordinate D j x) : C00 𝕜) =
    completedCoordinate D j x • Finsupp.single j (1 : 𝕜)
  simp

theorem initialCoefficients_apply (D : ConstructionData 𝕜) (N : ℕ)
    (x : ShiftSpace D) (k : ℕ) :
    initialCoefficients D N x k = if k < N then completedCoordinate D k x else 0 := by
  classical
  simp [initialCoefficients, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem exists_unit_subspace_initial_coordinates_zero (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E) (B : ℕ) :
    ∃ y : ShiftSpace D, y ∈ E ∧ ‖y‖ = 1 ∧ ∀ k ≤ B, completedCoordinate D k y = 0 := by
  obtain ⟨y, hy, hynorm, hz⟩ := exists_unit_in_subspace_annihilating_finite_family E hE
    (fun i : Fin (B+1) => completedCoordinate D i.val)
  exact ⟨y, hy, hynorm, fun k hk => hz ⟨k, by omega⟩⟩

theorem exists_subspace_tail_approximation (D : ConstructionData 𝕜)
    (E : Submodule 𝕜 (ShiftSpace D)) (hE : ¬ FiniteDimensional 𝕜 E)
    (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : C00 𝕜, ∃ y : ShiftSpace D, x ∈ afterCutoff B ∧ y ∈ E ∧
      ‖y‖ = 1 ∧ ‖denseEmbedding D x - y‖ < ε := by
  obtain ⟨y, hy, hynorm, hz⟩ := exists_unit_subspace_initial_coordinates_zero D E hE B
  have hlim := initialSum_tendsto D y
  obtain ⟨N, hN⟩ := (hlim.eventually (Metric.ball_mem_nhds y hε)).exists
  refine ⟨initialCoefficients D N y, y, ?_, hy, hynorm, ?_⟩
  · intro k hk
    rw [initialCoefficients_apply]
    split_ifs <;> simp [hz k hk]
  · simpa only [Metric.mem_ball, dist_eq_norm, denseEmbedding_initialCoefficients] using hN

end ThesisCommon.GowersMaurey
