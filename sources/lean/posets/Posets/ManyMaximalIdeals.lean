import Posets.ManyMaximalIdealsCardinality
import Posets.ManyMaximalIdealsScalar
import Posets.IdealMaximalTransfer

/-! Corollary 8.6 from the scalar instance of Theorem 1.5. The proof uses
the actual maximal closed ideals and an exact equivalence of cardinalities. -/
noncomputable section
open ThesisCommon
namespace Posets

theorem corollary_8_6_of_scalar_theorem_1_5 (𝕜 : Type) [RCLike 𝕜]
    (hquot : Theorem_1_5 𝕜 (fun _ : ℕ => 𝕜)) : Corollary_8_6 𝕜 := by
  letI : Nontrivial (ScalarBoundedProduct 𝕜) :=
    (lpUltrafilterEvaluation_surjective (𝕜 := 𝕜) (pure 0)).nontrivial
  obtain ⟨𝒜, h𝒜, θ, ρ, hs, _, _⟩ := hquot (fun _ => admissible_scalar)
  exact ⟨𝒜, h𝒜, ⟨(strongSplitMaximalIdealEquiv θ ρ hs h𝒜).symm.trans
    scalarBoundedProductMaximalIdealsEquiv⟩⟩

theorem corollary_8_6_of_theorem_1_5 (𝕜 : Type) [RCLike 𝕜]
    (hquot : ∀ (C : ℕ → Type) [∀ n, NormedRing (C n)]
      [∀ n, NormedAlgebra 𝕜 (C n)] [∀ n, CompleteSpace (C n)], Theorem_1_5 𝕜 C) :
    Corollary_8_6 𝕜 :=
  corollary_8_6_of_scalar_theorem_1_5 𝕜 (hquot (fun _ => 𝕜))

end Posets
