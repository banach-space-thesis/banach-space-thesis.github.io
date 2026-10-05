import Posets.TheoremQuotients
import Posets.SemisimpleQuotient
import Posets.TriangularTheoremTransfer
import Posets.ManyMaximalIdeals

/-! Unconditional applications of the proved product quotient theorem. -/

noncomputable section
namespace Posets

theorem corollary_1_7_proof (C : Type) [Ring C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] [IsSemisimpleRing C] : Corollary_1_7 C :=
  corollary_1_7_of_theorem_1_5 (theorem_1_5_proof ℂ) C

theorem exists_semisimple_quotient_algEquiv (C : Type) [Ring C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] [IsSemisimpleRing C] :
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (SeparableQuotient ℂ (Space ℂ 𝒜) ≃ₐ[ℂ] C) :=
  exists_semisimple_quotient_algEquiv_of_theorem_1_5 (theorem_1_5_proof ℂ) C

theorem theorem_1_8_proof (𝕜 : Type) [RCLike 𝕜] : Theorem_1_8 𝕜 :=
  theorem_1_8_of_1_5 𝕜 (theorem_1_5_proof 𝕜 _)

theorem corollary_8_6_proof (𝕜 : Type) [RCLike 𝕜] : Corollary_8_6 𝕜 :=
  corollary_8_6_of_scalar_theorem_1_5 𝕜 (theorem_1_5_proof 𝕜 _)

end Posets
