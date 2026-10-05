import JLMS.OrdinalSpaceInitialInfiniteReduction
import JLMS.OrdinalSpaceMultipleSquare
import JLMS.OrdinalSpaceOmega

/-!
# Assembly of the sufficient ordinal-space classification

Ordinal division isolates the three cases below κ², and logarithmic
normalization handles the remaining ordinals. This file isolates exactly
the two transfinite square constructions used by the final theorem:
singular initial ordinals and powers with exponent at least two.
The countable base and all reduction steps are already unconditional.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalSpaceReduction_of_initial_and_power_squares
    (hsingular : ∀ c : Cardinal.{u}, Cardinal.aleph0 ≤ c → ¬ c.IsRegular →
      Nonempty (OrdinalC 𝕜 c.ord ≃L[𝕜] OrdinalC 𝕜 c.ord × OrdinalC 𝕜 c.ord))
    (hpower : ∀ c : Cardinal.{u}, Cardinal.aleph0 ≤ c → ∀ γ : Ordinal.{u},
      2 ≤ γ → γ.card ≤ c → Nonempty (OrdinalC 𝕜 (c.ord ^ γ) ≃L[𝕜]
        OrdinalC 𝕜 (c.ord ^ γ) × OrdinalC 𝕜 (c.ord ^ γ)))
    (α : Ordinal.{u}) : OrdinalSpaceReduction 𝕜 α := by
  by_cases hfinite : α < Ordinal.omega0
  · exact Or.inl hfinite
  have hinf : Ordinal.omega0 ≤ α := le_of_not_gt hfinite
  let c : Cardinal.{u} := α.card
  have hc : Cardinal.aleph0 ≤ c := Ordinal.aleph0_le_card.mpr hinf
  have hκ : c.ord ≤ α := Cardinal.ord_card_le α
  by_cases hsmall : α < c.ord * Ordinal.omega0
  · by_cases hcount : c = Cardinal.aleph0
    · have homega : c.ord = Ordinal.omega0 := by rw [hcount, Cardinal.ord_aleph0]
      have he : Nonempty (OrdinalC 𝕜 c.ord ≃L[𝕜]
          OrdinalC 𝕜 c.ord × OrdinalC 𝕜 c.ord) := by
        rw [homega]
        exact ⟨ordinalSpaceOmegaSquareEquiv⟩
      exact ordinalSpaceReduction_of_initial_finiteQuotient_of_square c hc
        (Classical.choice he) α hκ hsmall
    · by_cases hreg : c.IsRegular
      · exact ordinalSpaceReduction_of_initial_finiteQuotient c hreg
          (lt_of_le_of_ne hc (Ne.symm hcount)) α hκ hsmall
      · exact ordinalSpaceReduction_of_initial_finiteQuotient_of_square c hc
          (Classical.choice (hsingular c hc hreg)) α hκ hsmall
  · have hlarge : c.ord * Ordinal.omega0 ≤ α := le_of_not_gt hsmall
    by_cases hsq : α ≤ c.ord * c.ord
    · exact ordinalSpaceReduction_of_initial_infiniteQuotient c hc α hlarge hsq
    · apply ordinalSpaceReduction_above_initial_square_of_powerSquares c hc α le_rfl
      · rw [← Ordinal.succ_one, Ordinal.opow_succ, Ordinal.opow_one]
        exact (lt_of_not_ge hsq).le
      · exact hpower c hc

end JLMS
