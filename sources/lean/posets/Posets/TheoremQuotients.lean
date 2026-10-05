import Posets.ProductQuotientRealizationTransport

/-! Theorem 1.5: every countable product of the stated admissible algebras is
the strongly split separable-range quotient of an actual Mrówka C₀ space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

theorem theorem_1_5_proof (𝕜 : Type) [RCLike 𝕜]
    (C : ℕ → Type) [∀ n, NormedRing (C n)] [∀ n, NormedAlgebra 𝕜 (C n)]
    [∀ n, CompleteSpace (C n)] : Theorem_1_5 𝕜 C := by
  intro hC
  let d : ∀ n, ProductQuotientComponent 𝕜 (C n) := fun n => quotientComponentOfAdmissible (hC n)
  obtain ⟨𝒜, had, θ, ρ, hs, hρ, _, hθone⟩ := exists_product_space_realization d
  exact ⟨𝒜, had, θ, ρ, hs, hρ, hθone⟩

end Posets
