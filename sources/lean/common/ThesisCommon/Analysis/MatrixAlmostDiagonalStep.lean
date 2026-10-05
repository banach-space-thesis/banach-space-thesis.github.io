import ThesisCommon.Analysis.MatrixBlockKillingUniform
import ThesisCommon.Analysis.BoundedProductFiniteTarget

/-! One step of the manuscript's almost-diagonalisation induction. The
past is an actual finite-dimensional subspace of the whole bounded product;
the future is an infinite coordinate band. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem matrixSumMask_eq_boundedProductMask (p : BanachExponent) (I : Set ℕ) :
    matrixSumMask (𝕜 := 𝕜) p I =
      boundedProductMask (𝕜 := 𝕜) (E := fun j => FiniteMatrixBlock 𝕜 p (j + 1)) I := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext j
  rw [matrixSumMask_apply, boundedProductMask_apply]

set_option maxHeartbeats 1200000 in
theorem exists_matrixAlmostDiagonal_step (p : BanachExponent)
    (hp : 1 < p.val.toReal) (hfin : p.val ≠ ∞)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (W : Submodule 𝕜 (FiniteMatrixSum 𝕜 p)) [FiniteDimensional 𝕜 W]
    (I : Set ℕ) (hI : I.Infinite) (k lower : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, n ∈ I ∧ k ≤ n ∧ lower ≤ n ∧
      ∃ (α τ : Fin (k + 1) ↪o Fin (n + 1)) (J : Set ℕ),
        J ⊆ I ∧ J.Infinite ∧ (∀ j ∈ J, n < j) ∧
        (∀ y : FiniteMatrixSum 𝕜 p, y ∈ W →
          ‖matrixBlockProjection (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding (T y n)‖ ≤
            b * ‖T y n‖) ∧
        ‖((matrixSumCoordinate (𝕜 := 𝕜) p n).comp T).comp
          (matrixSumMask (𝕜 := 𝕜) p J)‖ ≤ b := by
  classical
  obtain ⟨N₀, _, hsmall⟩ := exists_matrixBlock_small_on_subspace_finrank_le
    (𝕜 := 𝕜) p hp hfin (k + 1) (Module.finrank 𝕜 W) (Nat.succ_pos k) hb
  obtain ⟨n, hnI, hn⟩ := hI.exists_gt (max N₀ (max k lower))
  have hk : k ≤ n := (le_max_left k lower).trans ((le_max_right N₀ _).trans hn.le)
  have hlower : lower ≤ n := (le_max_right k lower).trans ((le_max_right N₀ _).trans hn.le)
  have hN : N₀ ≤ n + 1 := (le_max_left N₀ _).trans (hn.le.trans (Nat.le_succ n))
  let S := (matrixSumCoordinate (𝕜 := 𝕜) p n).comp T
  let E := W.map S.toLinearMap
  have hE : Module.finrank 𝕜 E ≤ Module.finrank 𝕜 W := Submodule.finrank_map_le _ _
  obtain ⟨α, τ, hblock⟩ := hsmall (n + 1) hN E hE
  letI : FiniteDimensional 𝕜 (FiniteMatrixBlock 𝕜 p (n + 1)) :=
    finiteMatrixBlock_finiteDimensional p (n + 1)
  obtain ⟨J, hJI, hJ, htail⟩ := boundedProductMask_finite_target_small S
    (I \ Set.Iic n) (hI.diff (Set.finite_Iic n)) hb
  refine ⟨n, hnI, hk, hlower, α, τ, J,
    (fun j hj => (hJI hj).1), hJ, ?_, ?_, ?_⟩
  · intro j hj
    exact lt_of_not_ge (hJI hj).2
  · intro y hy
    have hymem : S y ∈ E := ⟨y, hy, rfl⟩
    exact hblock ⟨S y, hymem⟩
  · rw [matrixSumMask_eq_boundedProductMask]
    exact htail.le

end ThesisCommon
