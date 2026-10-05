import PFP.MatrixStatements

/-! Apply the finite scalarisation hypothesis at a genuinely increasing
sequence of ambient dimensions. The remaining finite theorem is an explicit
premise of this intermediate lemma, not an axiom or a completed result. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem matrixDiagonal_component_norm_le (p : BanachExponent)
    (D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p)
    (F : ∀ n, MatrixBlock 𝕜 p (n+1) →L[𝕜] MatrixBlock 𝕜 p (n+1))
    (hD : ∀ x n, D x n = F n (x n)) (n : ℕ) : ‖F n‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (F n) D.opNorm_nonneg
  intro x
  let z : MatrixSum 𝕜 p := lp.single ∞ n x
  have hz : ‖z‖ = ‖x‖ := by
    exact lp.norm_single (E := fun k : ℕ => MatrixBlock 𝕜 p (k+1))
      (by simp : (0 : ℝ≥0∞) < ∞) n x
  have heq : D z n = F n x := by rw [hD]; simp [z]
  calc
    ‖F n x‖ = ‖D z n‖ := congrArg norm heq.symm
    _ ≤ ‖D z‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero (D z) n
    _ ≤ ‖D‖ * ‖z‖ := D.le_opNorm z
    _ = _ := by rw [hz]

theorem exists_matrix_scalarisation_sequence (p : BanachExponent)
    (hFinite : FiniteMatrixScalarisation 𝕜 p)
    (D : MatrixSum 𝕜 p →L[𝕜] MatrixSum 𝕜 p)
    (F : ∀ n, MatrixBlock 𝕜 p (n+1) →L[𝕜] MatrixBlock 𝕜 p (n+1))
    (hD : ∀ x n, D x n = F n (x n)) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, n ≤ m n) ∧
      ∀ n, ∃ (α τ : Fin (n+1) ↪o Fin (m n+1)),
        HasMatrixInverseBound 𝕜 p (n+1)
          (((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp (F (m n))).comp
            (matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)) 4 ∨
        HasMatrixInverseBound 𝕜 p (n+1)
          (((matrixRestrict (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding).comp
            (ContinuousLinearMap.id 𝕜 _ - F (m n))).comp
            (matrixInsert (𝕜 := 𝕜) p α.toEmbedding τ.toEmbedding)) 4 := by
  classical
  let K : ℝ := max 1 ‖D‖
  have hK : 1 ≤ K := le_max_left _ _
  have hcut (n : ℕ) := hFinite (n+1) (by omega) K (1/8) hK
    (by norm_num) (by norm_num)
  choose N₀ hN₀ hN using hcut
  let m : ℕ → ℕ := fun n => Nat.rec (N₀ 0) (fun j prev => max (N₀ (j+1)) (prev+1)) n
  have hmstep (n : ℕ) : m n < m (n+1) := by
    change m n < max (N₀ (n+1)) (m n+1)
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hm : StrictMono m := strictMono_nat_of_lt_succ hmstep
  have hmN (n : ℕ) : N₀ n ≤ m n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  refine ⟨m, hm, fun n => hm.id_le n, ?_⟩
  intro n
  have hFn : ‖F (m n)‖ ≤ K := (matrixDiagonal_component_norm_le p D F hD _).trans (le_max_right _ _)
  have hmNn := hmN n
  obtain ⟨α, τ, c, _, _, hinv⟩ := hN n (m n+1) (by omega) (F (m n)) hFn
  exact ⟨α, τ, hinv⟩

end PFP
