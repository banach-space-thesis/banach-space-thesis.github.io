import PFP.MainStatements
import ThesisCommon.Analysis.MatrixSumOperators
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Exact outstanding targets from the finite-matrix and growing-matrix-sum
section. These definitions are specifications, not proofs. The spaces,
matrix units, entry functionals, block maps, masks and norms are concrete.
Finite dimensions n,N,k below are literal cardinalities; hypotheses >0
encode the source's positive indexing. Product coordinate n represents X_(n+1).
-/
noncomputable section
open scoped ENNReal BigOperators
namespace PFP
open ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

local instance matrixSupportNormedSpace (p : BanachExponent) (I : Set ℕ) :
    NormedSpace 𝕜 (matrixSumSupport (𝕜 := 𝕜) p I) :=
  Submodule.normedSpace (𝕜 := 𝕜) (matrixSumSupport (𝕜 := 𝕜) p I)

/-- Lemma 5.6: both column and row unit-sum formulas, including arbitrary
unimodular coefficients. The exponent q is exactly p/(p-1). -/
def Lemma_5_6 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ → ∀ N : ℕ,
    ∀ (I J : Finset (Fin N)), I.Nonempty → J.Nonempty →
    ∀ (ε δ : Fin N → 𝕜), (∀ i ∈ I, ‖ε i‖ = 1) → (∀ j ∈ J, ‖δ j‖ = 1) →
    ∀ i₀ j₀ : Fin N,
      ‖∑ i ∈ I, ε i • matrixUnit (𝕜 := 𝕜) p i j₀‖ = (I.card : ℝ) ^ (1 / p.val.toReal) ∧
      ‖∑ j ∈ J, δ j • matrixUnit (𝕜 := 𝕜) p i₀ j‖ =
        (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1)))

/-- A bounded two-sided inverse on the actual operator space. -/
def HasMatrixInverseBound (p : BanachExponent) (n : ℕ)
    (S : MatrixBlock 𝕜 p n →L[𝕜] MatrixBlock 𝕜 p n) (C : ℝ) : Prop :=
  ∃ R : MatrixBlock 𝕜 p n →L[𝕜] MatrixBlock 𝕜 p n,
    R.comp S = ContinuousLinearMap.id 𝕜 _ ∧ S.comp R = ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ C

/-- Scalar-polymorphic finite scalarisation specification. Ordered embeddings
enumerate exactly the two n-element subsets; their ranges must be disjoint. -/
def FiniteMatrixScalarisation (p : BanachExponent) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ K ε : ℝ, 1 ≤ K → 0 < ε → ε < 1 / 4 →
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : MatrixBlock 𝕜 p N →L[𝕜] MatrixBlock 𝕜 p N, ‖T‖ ≤ K →
        ∃ (α τ : Fin n ↪o Fin N) (c : 𝕜),
          Disjoint (Set.range α) (Set.range τ) ∧
          ‖((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp T).comp
              (matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding) -
                c • ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p n)‖ < ε ∧
          (HasMatrixInverseBound 𝕜 p n
            (((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp T).comp
              (matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)) 4 ∨
           HasMatrixInverseBound 𝕜 p n
            (((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp
              (ContinuousLinearMap.id 𝕜 (MatrixBlock 𝕜 p N) - T)).comp
                (matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)) 4)

/-- Proposition 5.7 as printed: the scalar selected by the finite Ramsey
argument belongs to ℂ. MatrixScalarisationProofs proves the generic predicate
above and specializes it to this printed target. -/
def Proposition_5_7 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ → FiniteMatrixScalarisation ℂ p

/-- Lemma 5.8, both exact Hilbert–Schmidt/operator norm comparisons and the
strict exponent bound. The operator-space norm is never replaced by HS. -/
def Lemma_5_8 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    let a : ℝ := |1 / p.val.toReal - 1 / 2|
    a < 1 / 2 ∧
    (∀ N : ℕ, 0 < N → ∀ A : MatrixBlock 𝕜 p N,
      matrixHilbertSchmidtNorm p A ≤ (N : ℝ) ^ (1 / 2 + a) * ‖A‖) ∧
    (∀ k : ℕ, 0 < k → ∀ B : MatrixBlock 𝕜 p k,
      ‖B‖ ≤ (k : ℝ) ^ a * matrixHilbertSchmidtNorm p B)

/-- Lemma 5.9: the block projection is the actual J∘K, and the restriction
bound holds for every element of each d-dimensional operator subspace. -/
def Lemma_5_9 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ → ∀ k d : ℕ, 0 < k → 0 < d →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ E : Submodule 𝕜 (MatrixBlock 𝕜 p N), Module.finrank 𝕜 E = d →
        ∃ α τ : Fin k ↪o Fin N, ∀ x : E,
          ‖matrixBlockProjection p α.toEmbedding τ.toEmbedding (x : MatrixBlock 𝕜 p N)‖ ≤ ε * ‖x‖

/-- Lemma 5.10. F is an arbitrary finite-dimensional normed scalar space. -/
def Lemma_5_10 (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    ∀ (S : MatrixSum 𝕜 p →L[𝕜] F) (J : Set ℕ), J.Infinite →
      ∀ η : ℝ, 0 < η → ∃ I : Set ℕ, I ⊆ J ∧ I.Infinite ∧ ‖S.comp (matrixSumMask p I)‖ < η

/-- Lemma 5.11, retaining both compression equations for the same A,B.
The diagonal predicate requires action on all bounded product vectors. -/
def Lemma_5_11 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    ∀ (T : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p) (ε : ℝ), 0 < ε →
      ∃ A B T' D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p,
        ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ A.comp B = ContinuousLinearMap.id 𝕜 _ ∧
        T' = (A.comp T).comp B ∧ IsMatrixSumDiagonal p D ∧ ‖T' - D‖ < ε ∧
        ContinuousLinearMap.id 𝕜 _ - T' = ((A.comp (ContinuousLinearMap.id 𝕜 _ - T)).comp B)

/-- Lemma 5.12 in the concrete retraction form supplied by the source proof.
The range space is the actual full coordinate subspace supported on range n. -/
def Lemma_5_12 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    ∀ n : ℕ → ℕ, StrictMono n → (∀ j, j ≤ n j) →
      ∃ (E : MatrixSum 𝕜 p →L[𝕜] matrixSumSupport (𝕜 := 𝕜) p (Set.range n))
        (P : matrixSumSupport (𝕜 := 𝕜) p (Set.range n) →L[𝕜] MatrixSum 𝕜 p),
        ‖E‖ = 1 ∧ ‖P‖ = 1 ∧ P.comp E = ContinuousLinearMap.id 𝕜 _

/-- Proposition 5.13: the endpoint bound is exactly four, on genuine
coordinatewise diagonal operators on the entire bounded product. -/
def Proposition_5_13 : Prop :=
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    ∀ D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p, IsMatrixSumDiagonal p D →
      ∃ U V : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p,
        ((U.comp D).comp V = ContinuousLinearMap.id 𝕜 _ ∨
          (U.comp (ContinuousLinearMap.id 𝕜 _ - D)).comp V = ContinuousLinearMap.id 𝕜 _) ∧
        ‖U‖ * ‖V‖ ≤ 4

end PFP
