import PFP.MainStatements
import ThesisCommon.Analysis.InfinityWeakStarAdjoint

/-! Corollary 3.20. Weak-star continuity uses mathlib's `WeakDual` topology,
transported through the proved canonical isometric ℓ₁–ℓ∞ duality. -/
noncomputable section
open scoped ENNReal
namespace PFP
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Source `cor: weak-star-continuity`: the actual coordinate compression
on ℓ∞(M) is continuous for σ(ℓ∞(M),ℓ₁(M)). -/
def Corollary_3_20 : Prop :=
  ∀ T : ScalarEllInfinity 𝕜 →L[𝕜] ScalarEllInfinity 𝕜,
    ∃ M : Set ℕ, M.Infinite ∧
      @Continuous _ _ (infinityWeakStarTopology 𝕜 M) (infinityWeakStarTopology 𝕜 M)
        (infinityWeakStarCompression T M)

theorem corollary_3_20 : Corollary_3_20 (𝕜 := 𝕜) := by
  intro T
  obtain ⟨M, _, hM, hrep⟩ := infinity_matrix_restriction T
    (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  exact ⟨M, hM, infinityWeakStarCompression_continuous T hrep⟩

end PFP
