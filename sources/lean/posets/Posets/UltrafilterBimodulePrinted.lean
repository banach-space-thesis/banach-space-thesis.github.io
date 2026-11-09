import Posets.UltrafilterSynchronizationExact
import Posets.UltrafilterBimoduleExact

/-! Lemma 8.2 for the arbitrary finite block families of the article. -/
noncomputable section
open Filter
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets

def Lemma_8_2_exact (𝕜 : Type) [RCLike 𝕜] (I : ℕ → Type*)
    [∀ k, Finite (I k)] (U : Ultrafilter (ExactRowDomain I))
    (V : Ultrafilter (ExactColumnDomain I)) : Prop :=
  (∀ k, (k + 1) * 2 ^ (k + 1) ≤ Nat.card (I k)) →
  ExactSynchronized U V →
  ∃ L : OffDiagonalOn 𝕜 (ExactRowDomain I) (ExactColumnDomain I) →ₗ[𝕜] 𝕜,
    ¬ Continuous L ∧
    (∀ (a : Discrete (ExactRowDomain I) →ᵇ 𝕜)
        (T : OffDiagonalOn 𝕜 (ExactRowDomain I) (ExactColumnDomain I)),
      L ((multiplicationOperator a).comp T) =
        limUnder (U : Filter (ExactRowDomain I)) (fun x => a ⟨x⟩) * L T) ∧
    (∀ (b : Discrete (ExactColumnDomain I) →ᵇ 𝕜)
        (T : OffDiagonalOn 𝕜 (ExactRowDomain I) (ExactColumnDomain I)),
      L (T.comp (multiplicationOperator b)) =
        L T * limUnder (V : Filter (ExactColumnDomain I)) (fun x => b ⟨x⟩))

theorem lemma_8_2_exact_proof (𝕜 : Type) [RCLike 𝕜] (I : ℕ → Type*)
    [∀ k, Finite (I k)] (U : Ultrafilter (ExactRowDomain I))
    (V : Ultrafilter (ExactColumnDomain I)) : Lemma_8_2_exact 𝕜 I U V := by
  intro _ h
  exact lemma_8_2_of_finite_fibers 𝕜 (exactSelector (I := I))
    (exactSelector_finite_fiber (I := I)) U V h.2.2.1 h.2.2.2

end Posets
