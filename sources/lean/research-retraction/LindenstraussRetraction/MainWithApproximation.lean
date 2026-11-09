import LindenstraussRetraction.MainTheorem
import LindenstraussRetraction.BasisApproximation

/-! The main counterexample and the final approximation application on the same space. -/

noncomputable section
open Filter Topology

namespace LindenstraussRetraction

variable (𝕜 : Type) [RCLike 𝕜] [TopologicalSpace.SeparableSpace 𝕜]

/-- The manuscript's counterexample also admits compact-range bidual
approximations with common Lipschitz constant one. Every conclusion refers
to the same separable Banach-space witness. -/
theorem mainWithApproximation :
    ∃ X : SeparableBanachSpace.{0, 0} 𝕜,
      HasBimonotoneSchauderBasis 𝕜 X.Carrier ∧
      (¬ HasUniformUnitBallBidualRetraction 𝕜 X.Carrier) ∧
      (¬ HasUniformBidualRetraction 𝕜 X.Carrier) ∧
      (¬ HasLipschitzBidualRetraction 𝕜 X.Carrier) ∧
      ∃ Ψ : ℕ → Bidual 𝕜 X.Carrier → X.Carrier,
        (∀ N, LipschitzWith 1 (Ψ N)) ∧
        (∀ N, IsCompact (closure (Set.range (Ψ N)))) ∧
        ∀ x : X.Carrier,
          Tendsto (fun N => Ψ N (bidualEmbedding 𝕜 X.Carrier x)) atTop (𝓝 x) := by
  obtain ⟨X, ⟨b, hb⟩, hball, huniform, hlip⟩ := mainTheorem 𝕜
  exact ⟨X, ⟨b, hb⟩, hball, huniform, hlip,
    basis_has_one_lipschitz_compactRange_approximation b hb.1⟩

end LindenstraussRetraction
