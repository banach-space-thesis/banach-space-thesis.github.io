import ThesisCommon.Analysis.MatrixBlockKilling
import ThesisCommon.Analysis.MatrixFiniteDimension

/-! One cutoff handles every subspace of dimension at most d, including
the zero subspace. This is the version used in the successive-block recursion. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_matrixBlock_small_on_subspace_finrank_le (p : BanachExponent)
    (hp : 1 < p.val.toReal) (hfin : p.val ≠ ∞) (k d : ℕ) (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ E : Submodule 𝕜 (FiniteMatrixBlock 𝕜 p N), Module.finrank 𝕜 E ≤ d →
        ∃ α τ : Fin k ↪o Fin N, ∀ x : E,
          ‖matrixBlockProjection p α.toEmbedding τ.toEmbedding (x : FiniteMatrixBlock 𝕜 p N)‖ ≤ ε * ‖x‖ := by
  classical
  have hdim (r : Fin (d + 1)) :
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ E : Submodule 𝕜 (FiniteMatrixBlock 𝕜 p N), Module.finrank 𝕜 E = r.val →
          ∃ α τ : Fin k ↪o Fin N, ∀ x : E,
            ‖matrixBlockProjection p α.toEmbedding τ.toEmbedding (x : FiniteMatrixBlock 𝕜 p N)‖ ≤ ε * ‖x‖ := by
    by_cases hr : r.val = 0
    · refine ⟨k, hk, ?_⟩
      intro N hN E hE
      letI : FiniteDimensional 𝕜 (FiniteMatrixBlock 𝕜 p N) := finiteMatrixBlock_finiteDimensional p N
      haveI : FiniteDimensional 𝕜 E := inferInstance
      haveI : Subsingleton E := Module.finrank_zero_iff.mp (hE.trans hr)
      refine ⟨Fin.castLEOrderEmb hN, Fin.castLEOrderEmb hN, ?_⟩
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    · exact exists_matrixBlock_small_on_subspace p hp hfin k r.val hk (Nat.pos_of_ne_zero hr) hε
  choose M hM hworks using hdim
  let N₀ := ∑ r : Fin (d + 1), M r
  have hle (r : Fin (d + 1)) : M r ≤ N₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  refine ⟨N₀, (hM 0).trans_le (hle 0), ?_⟩
  intro N hN E hE
  let r : Fin (d + 1) := ⟨Module.finrank 𝕜 E, Nat.lt_succ_of_le hE⟩
  exact hworks r N ((hle r).trans hN) E rfl

end ThesisCommon
