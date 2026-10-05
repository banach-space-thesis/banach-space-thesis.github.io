import ThesisCommon.Analysis.DisjointSequenceBlocks
import ThesisCommon.Analysis.SequenceCoordinates
import ThesisCommon.Analysis.SupRowOperators

/-! The actual isomorphism ℓ∞(ℓ∞(X)) ≃ ℓ∞(X), using the pairing bijection
on natural numbers. Both directions are contractions and are inverses on all
bounded sequences, with no finite-support density assertion.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def infinityFlatten : EllInfinitySum (EllInfinitySum X) →L[𝕜] EllInfinitySum X :=
  infinityRows (fun n => (lpCoordinate ∞ (Nat.unpair n).2).comp
    (lpCoordinate ∞ (Nat.unpair n).1)) 1 zero_le_one (by
      intro n
      calc
        _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := X) ∞ (Nat.unpair n).2‖ *
            ‖lpCoordinate (𝕜 := 𝕜) (X := EllInfinitySum X) ∞ (Nat.unpair n).1‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := mul_le_mul (norm_lpCoordinate_le ∞ _) (norm_lpCoordinate_le ∞ _)
          (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)

def infinityUnflatten : EllInfinitySum X →L[𝕜] EllInfinitySum (EllInfinitySum X) :=
  infinityRows (fun i => lpRestrict ∞ (disjointCoordinateEmbedding i))
    1 zero_le_one (fun i => norm_lpRestrict_le (disjointCoordinateEmbedding i))

/-- Countable pairing supplies the self-similarity required for primariness. -/
def infinityFlattenEquiv : EllInfinitySum (EllInfinitySum X) ≃L[𝕜] EllInfinitySum X :=
  ContinuousLinearEquiv.equivOfInverse infinityFlatten infinityUnflatten
    (by
      intro x
      ext i j
      change x (Nat.unpair (Nat.pair i j)).1 (Nat.unpair (Nat.pair i j)).2 = x i j
      rw [Nat.unpair_pair])
    (by
      intro x
      ext n
      change x (Nat.pair (Nat.unpair n).1 (Nat.unpair n).2) = x n
      rw [Nat.pair_unpair])

theorem infinity_sequenceSelfSimilar : IsSequenceSelfSimilar 𝕜 (EllInfinitySum X) :=
  Or.inl ⟨⟨∞, le_top⟩, ⟨infinityFlattenEquiv.symm⟩⟩

end ThesisCommon
