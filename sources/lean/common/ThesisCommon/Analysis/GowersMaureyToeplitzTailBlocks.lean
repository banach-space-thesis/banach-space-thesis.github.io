import ThesisCommon.Analysis.GowersMaureyToeplitzBlocks
import ThesisCommon.Analysis.GowersMaureyLaurentIsometry
import ThesisCommon.Analysis.GowersMaureyBlockTails

/-! Finite-band Laurent tests at arbitrary coordinate cutoffs. The
offset cancels in every matrix entry, so the coefficient lower bound is
unchanged. These are actual finite vectors, not formal matrix tests. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def toeplitzTailVector (𝕜 : Type*) [RCLike 𝕜] (M r B : ℕ) : C00 𝕜 :=
  ∑ t : Fin r, Finsupp.single (B+1+(2*M+1)*t.val+M) (1 : 𝕜)

theorem toeplitzTailVector_mem_afterCutoff (M r B : ℕ) :
    toeplitzTailVector 𝕜 M r B ∈ afterCutoff B := by
  intro k hk
  simp only [toeplitzTailVector, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  exact Finsupp.single_eq_of_ne (by omega)

theorem toeplitzTailVector_denseEmbedding (D : ConstructionData 𝕜) (M r B : ℕ) :
    denseEmbedding D (toeplitzTailVector 𝕜 M r B) =
      ∑ t : Fin r, basisVector D (B+1+(2*M+1)*t.val+M) := by
  simp only [toeplitzTailVector, map_sum, basisVector, PreSpace.single]

theorem laurent_tail_block_coordinate (D : ConstructionData 𝕜) (M r B : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    (i : Fin r) (j : Fin (2*M+1)) :
    completedCoordinate D (B+1+(2*M+1)*i.val+j.val)
      (laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B))) =
      a ((j.val : ℤ) - M) := by
  classical
  rw [toeplitzTailVector_denseEmbedding, map_sum, map_sum, Finset.sum_eq_single i]
  · change matrixEntry D _ _ (laurentOperator D a) = _
    rw [matrixEntry_laurentOperator]
    apply congrArg (fun d : ℤ => a d)
    push_cast
    ring
  · intro t _ hti
    change matrixEntry D _ _ (laurentOperator D a) = _
    rw [matrixEntry_laurentOperator]
    apply hband
    have hh := toeplitz_block_difference_outside
      (M := M) (i := i.val) (t := t.val) (j := j.val)
      (by intro h; apply hti; exact Fin.ext h.symm) j.isLt
    push_cast at hh ⊢
    rcases hh with hh | hh <;> omega
  · simp

theorem laurent_tail_block_coordinate_sum (D : ConstructionData 𝕜) (M r B : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0) :
    (∑ k : Fin (r*(2*M+1)), ‖completedCoordinate D (B+1+k.val)
      (laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B)))‖) =
      (r : ℝ) * ‖a‖ := by
  have he := (finProdFinEquiv : Fin r × Fin (2*M+1) ≃ Fin (r*(2*M+1))).sum_comp
    (fun k => ‖completedCoordinate D (B+1+k.val)
      (laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B)))‖)
  rw [← he, Fintype.sum_prod_type]
  have hb : ∀ i : Fin r, ∀ j : Fin (2*M+1),
      ‖completedCoordinate D (B+1+(finProdFinEquiv (i,j)).val)
        (laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B)))‖ =
        ‖a ((j.val : ℤ)-M)‖ := by
    intro i j
    have hh := laurent_tail_block_coordinate D M r B a hband i j
    change ‖completedCoordinate D (B+1+(j.val+(2*M+1)*i.val)) _‖ = _
    rw [Nat.add_comm j.val, ← Nat.add_assoc, hh]
  simp_rw [hb]
  rw [wiener_norm_eq_band_sum M a hband]
  simp

theorem laurent_tail_vector_norm_lower (D : ConstructionData 𝕜) (M r B : ℕ)
    (a : WienerSequences 𝕜) (hband : ∀ d : ℤ, d < -(M : ℤ) ∨ (M : ℤ) < d → a d = 0)
    (hr : 2 ≤ r) :
    ((r : ℝ) / logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ)) * ‖a‖ ≤
      ‖laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B))‖ := by
  have hrc : 2 ≤ r*(2*M+1) := by nlinarith
  have hfc : 0 < logarithmicWeight ((r*(2*M+1) : ℕ) : ℝ) :=
    zero_lt_one.trans_le (one_le_logarithmicWeight (by omega))
  have hcoord := completedCoordinate_sum_norm_le_weight D hrc
    (show StrictMono (fun k : Fin (r*(2*M+1)) => B+1+k.val) from
      fun _ _ h => Nat.add_lt_add_left h _)
    (laurentOperator D a (denseEmbedding D (toeplitzTailVector 𝕜 M r B)))
  rw [laurent_tail_block_coordinate_sum D M r B a hband] at hcoord
  rw [div_mul_eq_mul_div, div_le_iff₀ hfc]
  exact hcoord.trans_eq (mul_comm _ _)

end ThesisCommon.GowersMaurey
