import PFP.MatrixStatements
import ThesisCommon.Analysis.MatrixScalarisation
import ThesisCommon.Analysis.ScalarInverseDichotomy

/-! Proposition 5.7 on the actual finite-lp matrix operator spaces, with
ordered disjoint blocks, uniform cutoff and genuine two-sided inverses. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem finiteMatrixScalarisation (p : BanachExponent) (hp : 1 < p.val.toReal) :
    FiniteMatrixScalarisation 𝕜 p := by
  intro n hn K ε hK hε hεquarter
  obtain ⟨N₀, hN₀, hselect⟩ := exists_matrix_scalarisation (𝕜 := 𝕜) p hp n hn
    (lt_of_lt_of_le zero_lt_one hK) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN T hT
  obtain ⟨α, τ, c, hdisj, hclose⟩ := hselect N hN T hT
  refine ⟨α, τ, c, hdisj, hclose, ?_⟩
  let S := ((matrixRestrict p α.toEmbedding τ.toEmbedding).comp T).comp
    (matrixInsert p α.toEmbedding τ.toEmbedding)
  have hclose' : ‖S - c • ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p n)‖ ≤ 1 / 4 :=
    (hclose.trans hεquarter).le
  have hcomplement :
      ((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp
        (ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p N) - T)).comp
          (matrixInsert p α.toEmbedding τ.toEmbedding) =
        ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p n) - S := by
    apply ContinuousLinearMap.ext
    intro x
    change matrixRestrict p α.toEmbedding τ.toEmbedding
      (matrixInsert p α.toEmbedding τ.toEmbedding x -
        T (matrixInsert p α.toEmbedding τ.toEmbedding x)) = x - S x
    rw [map_sub]
    exact congrArg (fun z => z - S x)
      (DFunLike.congr_fun (matrixRestrict_comp_insert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding) x)
  rcases exists_inverse_or_complement_of_near_scalar S c hclose' with h | h
  · exact Or.inl h
  · right
    unfold HasMatrixInverseBound
    rw [hcomplement]
    exact h

theorem proposition_5_7 : Proposition_5_7 := by
  intro p hp hfin
  apply finiteMatrixScalarisation ℂ p
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hfin).mpr hp

end PFP

