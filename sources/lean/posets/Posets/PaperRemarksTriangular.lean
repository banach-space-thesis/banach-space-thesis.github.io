import Posets.MainTheorem
import Posets.CountableStrongSplit
import Posets.PosetFamilyEmbedding

/-! The mathematical consequence in Remark 6.23. Every countable incidence
pattern in the opposite order is a genuine strongly split operator quotient.
The usual orders on ℕ and its dual give the two triangular orientations. -/

noncomputable section
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000

theorem remark_6_23_countable_incidence_quotient (P : Type) [PartialOrder P] [Countable P] :
    ∃ 𝒜 : BoundedExtension P → Set (Set ℕ),
      (∀ p, IsAlmostDisjoint (𝒜 p) ∧ JFA.HasContinuumSize (𝒜 p)) ∧
      let Y := DependentCZeroSum 𝕜 (fun p : P => Space 𝕜 (𝒜 (middle p)))
      ∃ C : Subalgebra 𝕜 (CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P),
        (C : Set _) = oppositeIncidenceOperators 𝕜 P ∧
        ∃ θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
        ∃ ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y), StrongSplit 𝕜 Y C θ ρ := by
  obtain ⟨𝒜, h𝒜, ι, hfew⟩ := continuum_fewOperators 𝕜
    (countablePosetSetEmbedding (BoundedExtension P))
  refine ⟨𝒜, h𝒜, ?_⟩
  exact proposition_6_22_proof 𝕜 P (fun p => Space 𝕜 (𝒜 p)) ι hfew

end Posets
