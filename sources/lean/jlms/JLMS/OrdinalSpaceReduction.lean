import JLMS.OrdinalSpaceFinite
import JLMS.OrdinalSpaceFinitePower
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Assembling the three branches of Section 9

`OrdinalSpaceReduction` states exactly the consequence of the ordinal-space
classification needed in the paper: a finite ordinal, a square-isomorphic
space, or a finite power of a regular uncountable initial-ordinal space.
This file proves the assembly from that reduction and Ogden's theorem.
The reduction itself is an explicit mathematical input, not an asserted theorem.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

def OrdinalSpaceReduction (𝕜 : Type w) [RCLike 𝕜] (α : Ordinal.{u}) : Prop :=
  α < Ordinal.omega0 ∨
  (Ordinal.omega0 ≤ α ∧ Nonempty (OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (α * 2))) ∨
  ∃ c : Cardinal.{u}, c.IsRegular ∧ Cardinal.aleph0 < c ∧
    ∃ n : ℕ, Nonempty
      (OrdinalC 𝕜 α ≃L[𝕜] OrdinalC 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)))

theorem theorem_1_3_of_ordinalSpaceReduction (α : Ordinal.{u})
    (hα : OrdinalSpaceReduction 𝕜 α)
    (hOgden : ∀ c : Cardinal.{u}, c.IsRegular → Cardinal.aleph0 < c →
      Theorem_1_3.{u, v, w} 𝕜 c.ord) : Theorem_1_3.{u, v, w} 𝕜 α := by
  rcases hα with hfinite | ⟨hinf, ⟨e⟩⟩ | ⟨c, hc, hu, n, ⟨e⟩⟩
  · exact theorem_1_3_of_lt_omega0 α hfinite
  · intro A _ _ _ _ _ φ
    exact continuous_ordinal_hom_of_doubleIsomorphic α hinf e φ
  · intro A _ _ _ _ _ φ
    have hκ : Ordinal.omega0 ≤ c.ord := by
      simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr hu.le
    apply continuous_operator_hom_of_conjugation e φ
    exact continuous_ordinal_hom_of_finiteMultiple c.ord hκ n (hOgden c hc hu A) _

end JLMS
