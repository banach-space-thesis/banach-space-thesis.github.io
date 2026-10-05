import ThesisCommon.Analysis.MatrixAlmostDiagonalStep
import ThesisCommon.Analysis.MatrixAlmostDiagonalData

/-! The source induction for almost diagonalisation. At each stage the
finite-dimensional past grows by one actual inserted matrix block, and the
infinite future band is thinned after the new block has been selected. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

private structure MatrixSelectionState (p : BanachExponent) where
  past : Submodule 𝕜 (FiniteMatrixSum 𝕜 p)
  finite : FiniteDimensional 𝕜 past
  band : Set ℕ
  infinite : band.Infinite
  lower : ℕ

private structure MatrixSelectionChoice (p : BanachExponent)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (b : ℕ → ℝ) (k : ℕ) (st : MatrixSelectionState (𝕜 := 𝕜) p) where
  n : ℕ
  mem_band : n ∈ st.band
  ge_index : k ≤ n
  ge_lower : st.lower ≤ n
  row : Fin (k + 1) ↪o Fin (n + 1)
  col : Fin (k + 1) ↪o Fin (n + 1)
  band : Set ℕ
  subset : band ⊆ st.band
  infinite : band.Infinite
  beyond : ∀ j ∈ band, n < j
  past_small : ∀ y : FiniteMatrixSum 𝕜 p, y ∈ st.past →
    ‖matrixBlockProjection (𝕜 := 𝕜) p row.toEmbedding col.toEmbedding (T y n)‖ ≤
      b k * ‖T y n‖
  future_small :
    ‖((matrixSumCoordinate (𝕜 := 𝕜) p n).comp T).comp
      (matrixSumMask (𝕜 := 𝕜) p band)‖ ≤ b k

private def matrixSelectionChoose (p : BanachExponent)
    (hp : 1 < p.val.toReal) (hfin : p.val ≠ ∞)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) (k : ℕ) (st : MatrixSelectionState (𝕜 := 𝕜) p) :
    MatrixSelectionChoice p T b k st := by
  letI : FiniteDimensional 𝕜 st.past := st.finite
  exact Classical.choice (by
    obtain ⟨n, hn, hk, hl, α, τ, J, hJI, hJ, hJb, hW, htail⟩ :=
      exists_matrixAlmostDiagonal_step p hp hfin T st.past st.band st.infinite k st.lower (hb k)
    exact ⟨⟨n, hn, hk, hl, α, τ, J, hJI, hJ, hJb, hW, htail⟩⟩)

private def matrixSelectionAdvance (p : BanachExponent)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (b : ℕ → ℝ) (k : ℕ) (st : MatrixSelectionState (𝕜 := 𝕜) p)
    (w : MatrixSelectionChoice p T b k st) : MatrixSelectionState (𝕜 := 𝕜) p := by
  letI : FiniteDimensional 𝕜 st.past := st.finite
  letI : FiniteDimensional 𝕜 (FiniteMatrixBlock 𝕜 p (k + 1)) :=
    finiteMatrixBlock_finiteDimensional p (k + 1)
  let f := (matrixSumSingle (𝕜 := 𝕜) p w.n).comp
    (matrixInsert (𝕜 := 𝕜) p w.row.toEmbedding w.col.toEmbedding)
  exact
    { past := st.past ⊔ LinearMap.range f.toLinearMap
      finite := inferInstance
      band := w.band
      infinite := w.infinite
      lower := w.n + 1 }

theorem exists_matrixAlmostDiagonalData (p : BanachExponent)
    (hp : 1 < p.val.toReal) (hfin : p.val ≠ ∞)
    (T : FiniteMatrixSum 𝕜 p →L[𝕜] FiniteMatrixSum 𝕜 p)
    (b : ℕ → ℝ) (hb : ∀ k, 0 < b k) : Nonempty (MatrixAlmostDiagonalData p T b) := by
  classical
  let init : MatrixSelectionState (𝕜 := 𝕜) p :=
    { past := ⊥
      finite := inferInstance
      band := Set.univ
      infinite := Set.infinite_univ
      lower := 0 }
  let states : ℕ → MatrixSelectionState (𝕜 := 𝕜) p :=
    Nat.rec init (fun k st => matrixSelectionAdvance p T b k st
      (matrixSelectionChoose p hp hfin T b hb k st))
  let choices (k : ℕ) := matrixSelectionChoose p hp hfin T b hb k (states k)
  have hs (k : ℕ) : states (k + 1) = matrixSelectionAdvance p T b k (states k) (choices k) := rfl
  refine ⟨{
    n := fun k => (choices k).n
    n_strictMono := ?_
    le_n := fun k => (choices k).ge_index
    row := fun k => (choices k).row
    col := fun k => (choices k).col
    band := fun k => (states k).band
    band_antitone := ?_
    n_mem_band := fun k => (choices k).mem_band
    past := fun k => (states k).past
    past_monotone := ?_
    single_mem_past := ?_
    past_small := fun k => (choices k).past_small
    future_small := ?_ }⟩
  · apply strictMono_nat_of_lt_succ
    intro k
    have h := (choices (k + 1)).ge_lower
    have hlower : (states (k + 1)).lower = (choices k).n + 1 :=
      congrArg (fun st : MatrixSelectionState (𝕜 := 𝕜) p => st.lower) (hs k)
    rw [hlower] at h
    exact h
  · apply antitone_nat_of_succ_le
    intro k
    rw [hs k]
    exact (choices k).subset
  · apply monotone_nat_of_le_succ
    intro k
    rw [hs k]
    exact le_sup_left
  · intro k x
    rw [hs k]
    apply Submodule.mem_sup_right
    exact (show (matrixSumSingle (𝕜 := 𝕜) p (choices k).n
      (matrixInsert (𝕜 := 𝕜) p (choices k).row.toEmbedding (choices k).col.toEmbedding x)) ∈
        LinearMap.range (((matrixSumSingle (𝕜 := 𝕜) p (choices k).n).comp
          (matrixInsert (𝕜 := 𝕜) p (choices k).row.toEmbedding
            (choices k).col.toEmbedding)).toLinearMap) from ⟨x, rfl⟩)
  · intro k
    rw [hs k]
    exact (choices k).future_small

end ThesisCommon
