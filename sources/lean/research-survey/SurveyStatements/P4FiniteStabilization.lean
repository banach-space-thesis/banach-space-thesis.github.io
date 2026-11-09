import SurveyStatements.P4RepeatedFramePaths
import SurveyStatements.P4FinitePathBasis

/-! Uniformly complemented finite-dimensional coefficient-path extensions. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Finset Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [FiniteDimensional 𝕜 E]
variable {N : ℕ}

abbrev RepeatedFrameSpace (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :=
  FinitePathSpace (𝕜 := 𝕜) (repeatedPathVectors b m hN)

def repeatedFrameEmbeddingLinearMap (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :
    E →ₗ[𝕜] RepeatedFrameSpace b m hN where
  toFun x := ⟨repeatedPathLinearMap b m hN x, ⟨repeatedPathCoefficients b m hN x, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact (repeatedPathLinearMap b m hN).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact (repeatedPathLinearMap b m hN).map_smul a x

def repeatedFrameEmbedding (b : Basis (Fin N) 𝕜 E) {m : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hbound : basisFrameBound b ≤ m) :
    E →L[𝕜] RepeatedFrameSpace b m hN :=
  (repeatedFrameEmbeddingLinearMap b m hN).mkContinuous 2
    (fun x => repeatedPathLinearMap_norm_le b hm hN hbound x)

def repeatedFrameRetraction (b : Basis (Fin N) 𝕜 E) (m : ℕ) (hN : 0 < N) :
    RepeatedFrameSpace b m hN →L[𝕜] E :=
  ({ toFun := fun f => f.val (Fin.last (m * N))
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : RepeatedFrameSpace b m hN →ₗ[𝕜] E).mkContinuous 1
    (fun f => by simpa using norm_le_pi_norm f.val (Fin.last (m * N)))

lemma repeatedFrameRetraction_comp_embedding (b : Basis (Fin N) 𝕜 E) {m : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hbound : basisFrameBound b ≤ m) :
    (repeatedFrameRetraction b m hN).comp (repeatedFrameEmbedding b hm hN hbound) =
      ContinuousLinearMap.id 𝕜 E := by
  apply ContinuousLinearMap.ext
  intro x
  exact repeatedPathLinearMap_last b hm hN x

lemma norm_repeatedFrameEmbedding_le_two (b : Basis (Fin N) 𝕜 E) {m : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hbound : basisFrameBound b ≤ m) :
    ‖repeatedFrameEmbedding b hm hN hbound‖ ≤ 2 := by
  apply (repeatedFrameEmbedding b hm hN hbound).opNorm_le_bound (by norm_num)
  intro x
  exact repeatedPathLinearMap_norm_le b hm hN hbound x

lemma norm_repeatedFrameRetraction_le_one (b : Basis (Fin N) 𝕜 E)
    (m : ℕ) (hN : 0 < N) : ‖repeatedFrameRetraction b m hN‖ ≤ 1 := by
  apply (repeatedFrameRetraction b m hN).opNorm_le_bound (by norm_num)
  intro f
  simpa using norm_le_pi_norm f.val (Fin.last (m * N))

/-- A positive-dimensional finite normed space has an actual finite basis
extension with uniform embedding and retraction bounds and basis constant one. -/
theorem exists_repeatedFrame_extension (b : Basis (Fin N) 𝕜 E) (hN : 0 < N) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ hbound : basisFrameBound b ≤ m,
      (repeatedFrameRetraction b m hN).comp (repeatedFrameEmbedding b hm hN hbound) =
        ContinuousLinearMap.id 𝕜 E ∧
      ‖repeatedFrameEmbedding b hm hN hbound‖ ≤ 2 ∧
      ‖repeatedFrameRetraction b m hN‖ ≤ 1 ∧
      ∀ k : Fin (m * N + 1),
        ‖finiteBasisPrefix (finitePathBasis (𝕜 := 𝕜) (repeatedPathVectors b m hN)
          (fun i => b.ne_zero (periodicFinIndex hN i.val))) k‖ ≤ 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (basisFrameBound b + 1)
  have hmpos : 0 < m := by
    have hb := basisFrameBound_nonneg b
    have h : (0 : ℝ) < m := by linarith
    exact_mod_cast h
  have hbound : basisFrameBound b ≤ m := by linarith
  refine ⟨m, hmpos, hbound, repeatedFrameRetraction_comp_embedding b hmpos hN hbound,
    norm_repeatedFrameEmbedding_le_two b hmpos hN hbound,
    norm_repeatedFrameRetraction_le_one b m hN, ?_⟩
  intro k
  exact finitePathBasis_prefix_norm_le_one (repeatedPathVectors b m hN)
    (fun i => b.ne_zero (periodicFinIndex hN i.val)) k

end SurveyStatements.P4
