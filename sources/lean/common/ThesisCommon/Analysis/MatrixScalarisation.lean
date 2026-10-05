import ThesisCommon.Analysis.MatrixCoefficientScalarisation
import ThesisCommon.Analysis.MatrixUnitCompression

/-! Uniform scalarisation in the actual finite-lp matrix operator norm. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_matrix_scalarisation (p : BanachExponent) (hp : 1 < p.val.toReal)
    (n : ℕ) (hn : 0 < n) {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N, ‖T‖ ≤ K →
      ∃ (α τ : Fin n ↪o Fin N) (c : 𝕜),
        Disjoint (Set.range α) (Set.range τ) ∧
        ‖((matrixRestrict p α.toEmbedding τ.toEmbedding).comp T).comp
            (matrixInsert p α.toEmbedding τ.toEmbedding) -
              c • ContinuousLinearMap.id 𝕜 (FiniteMatrixBlock 𝕜 p n)‖ < ε := by
  classical
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let δ := ε / (8 * (n : ℝ) ^ 3)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀, hN₀, hselect⟩ := exists_matrix_coefficient_scalarisation (𝕜 := 𝕜) p hp n hK hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN T hT
  obtain ⟨α, τ, c, hdisj, hcoeff⟩ := hselect N hN T hT
  refine ⟨α, τ, c, hdisj, ?_⟩
  let S : FiniteMatrixBlock 𝕜 p n →L[𝕜] FiniteMatrixBlock 𝕜 p n :=
    ((matrixRestrict p α.toEmbedding τ.toEmbedding).comp T).comp
    (matrixInsert p α.toEmbedding τ.toEmbedding)
  have hentry (i j k l : Fin n) :
      matrixEntry p i j ((S - c • ContinuousLinearMap.id 𝕜 (FiniteMatrixBlock 𝕜 p n)) (matrixUnit p k l)) =
        matrixEntry p (α i) (τ j) (T (matrixUnit p (α k) (τ l))) -
          (if i = k ∧ j = l then c else 0) := by
    simp only [S, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      matrixInsert_unit, map_sub, map_smul, matrixEntry_restrict, matrixEntry_unit_eq]
    split_ifs <;> simp
  have hnorm := matrixOperator_norm_le_of_coefficients_le p hp hn
    (S - c • ContinuousLinearMap.id 𝕜 (FiniteMatrixBlock 𝕜 p n)) hδ.le
    (fun i j k l => by rw [hentry]; exact hcoeff k l i j)
  have hnum : (n : ℝ)^3 * δ = ε / 8 := by
    dsimp [δ]
    field_simp
  exact hnorm.trans_lt (by rw [hnum]; linarith)

end ThesisCommon

