import Posets.Definitions
import PosetsCommon.FactorizationIdeal

/-! The maximal-ideal criterion used in Section 3, expressed using the paper's
literal bounded-operator factorisations. The ordinal-space splitting property
is a separate analytic obligation, not an assumption hidden in the definition. -/

noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem operator_identityNonfactorization_iff (T : E →L[𝕜] E) :
    T ∈ IdentityNonfactorization (E →L[𝕜] E) ↔ DoesNotFactorIdentity 𝕜 T E := by
  constructor
  · intro h hfactor
    obtain ⟨A, B, hAB⟩ := hfactor
    exact h ⟨B, A, by simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] using hAB⟩
  · intro h hfactor
    obtain ⟨A, B, hAB⟩ := hfactor
    exact h ⟨B, A, by simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc] using hAB⟩

theorem operator_identityNonfactorization_set :
    IdentityNonfactorization (E →L[𝕜] E) =
      {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T E} :=
  Set.ext operator_identityNonfactorization_iff

/-- The Dosev--Johnson algebraic step: the two-operator splitting property
makes the set of operators not factoring the identity the unique maximal ideal. -/
theorem uniqueMaximal_of_identity_split [Nontrivial E] [CompleteSpace E]
    (hsplit : ∀ T : E →L[𝕜] E,
      (∃ A B : E →L[𝕜] E, B.comp (T.comp A) = ContinuousLinearMap.id 𝕜 E) ∨
      (∃ A B : E →L[𝕜] E,
        B.comp ((ContinuousLinearMap.id 𝕜 E - T).comp A) = ContinuousLinearMap.id 𝕜 E)) :
    IsMaximalClosedIdeal 𝕜 {T : E →L[𝕜] E | DoesNotFactorIdentity 𝕜 T E} ∧
      HasUniqueMaximalClosedIdeal 𝕜 (E →L[𝕜] E) := by
  have hring : ∀ T : E →L[𝕜] E,
      (∃ A B : E →L[𝕜] E, A * T * B = 1) ∨
      (∃ A B : E →L[𝕜] E, A * (1 - T) * B = 1) := by
    intro T
    rcases hsplit T with ⟨A, B, h⟩ | ⟨A, B, h⟩
    · exact Or.inl ⟨B, A, by simpa only [ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc] using h⟩
    · exact Or.inr ⟨B, A, by simpa only [ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc] using h⟩
  simpa only [operator_identityNonfactorization_set] using
    identityNonfactorization_uniqueMaximalClosed (𝕜 := 𝕜) hring

end Posets
