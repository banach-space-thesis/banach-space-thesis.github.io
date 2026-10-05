import JLMS.Definitions

/-!
# Main results: statements only

Source: Antonio Acuaviva, JLMS 112 (2025), e70321.
https://doi.org/10.1112/jlms.70321

The comments transcribe the human statements (mathematical notation is adapted
to plain text). Numbering was checked against the local typeset author proof,
pages 2-4, and the publisher's HTML on 1 October 2026.

Each result is a `def ... : Prop`, NOT a theorem with a proof. There are no
asserted paper results, no proof placeholders, and no added axioms.
Type-checking these definitions checks that the statements are well-formed;
it does not prove the propositions or certify agreement with the prose.

Shared conventions: 𝕜 is ℝ or ℂ (represented by mathlib's RCLike class);
operators are bounded 𝕜-linear maps; all function-space norms are sup norms.
-/

noncomputable section

namespace JLMS

universe u v w

section ScatteredSpaces

/-- **Theorem 1.1** (page 2).

"Let K be a scattered, locally compact Hausdorff space and consider the Calkin
algebra B(C₀(K))/K(C₀(K)). Then the essential norm ‖·‖ₑ is minimal. In particular,
the Calkin algebra admits a unique complete algebra norm."

Both the main assertion and the 'in particular' clause are included.
-/
def Theorem_1_1 (𝕜 : Type*) [RCLike 𝕜]
    (K : Type*) [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K] : Prop :=
  IsScattered K →
    EssentialNormIsMinimal 𝕜 (CZero 𝕜 K) ∧
    HasUniqueCompleteCalkinNorm 𝕜 (CZero 𝕜 K)

/-- **Theorem 1.5** (page 3).

"Let K be a scattered, locally compact Hausdorff space and consider the Calkin
algebra B(C₀(K))/K(C₀(K)). Then the dual essential norm T ↦ ‖T*‖ₑ has Bonsall's
minimality property."
-/
def Theorem_1_5 (𝕜 : Type*) [RCLike 𝕜]
    (K : Type*) [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K] : Prop :=
  IsScattered K → DualEssentialNormHasBonsallMinimality 𝕜 (CZero 𝕜 K)

/-- **Theorem 1.6** (pages 3-4).

"Let K be a scattered, locally compact Hausdorff space and let X be a Banach space
that does not contain a copy of ℓ¹ or for which the unit ball of X* is weak*
sequentially compact. Then for any noncompact operator T : C₀(K) → X and any ε > 0,
there exist operators U ∈ B(X,c₀) and V ∈ B(c₀,C₀(K)) such that
  UTV = I_c₀ and ‖U‖ ‖V‖ < 2 / ‖T‖ₑ + ε."

The product bound is strict; ε is additive and follows the fraction.
U and V are chosen after T and ε. No separability assumption is added.
-/
def Theorem_1_6 (𝕜 : Type*) [RCLike 𝕜]
    (K : Type*) [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : Prop :=
  IsScattered K → AdmissibleCodomain 𝕜 X →
    ∀ T : CZero 𝕜 K →L[𝕜] X, ¬ IsCompactOperator T →
      ∀ ε : ℝ, 0 < ε →
        ∃ U : X →L[𝕜] cZero 𝕜,
        ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
          (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
          ‖U‖ * ‖V‖ < 2 / essentialNorm T + ε

/-- The set whose supremum occurs in Theorem 1.7.
The existential quantifiers range over ALL U and V of the specified types.
The identity equation forces both maps to be nonzero. -/
def factorizationValues (𝕜 : Type*) [RCLike 𝕜]
    (K : Type*) [TopologicalSpace K]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : CZero 𝕜 K →L[𝕜] X) : Set ℝ :=
  {r : ℝ | ∃ U : X →L[𝕜] cZero 𝕜,
    ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      r = ‖U‖⁻¹ * ‖V‖⁻¹}

/-- **Theorem 1.7** (page 4).

"Let K be a scattered, locally compact Hausdorff space and let X be a Banach space
that does not contain a copy of ℓ¹ or for which the unit ball of X* is weak*
sequentially compact. Then for any noncompact operator T : C₀(K) → X
  ‖T*‖ₑ = sup { ‖U‖⁻¹ ‖V‖⁻¹ : UTV = I_c₀ }."

The left side is the essential norm of the Banach adjoint, not that of T.
IsLUB says that ‖T*‖ₑ is the least upper bound, i.e. the displayed supremum.
This avoids Lean's totalized real sSup, which also assigns a value to an empty
or unbounded set. IsLUB asserts the mathematical supremum property directly.
-/
def Theorem_1_7 (𝕜 : Type*) [RCLike 𝕜]
    (K : Type*) [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : Prop :=
  IsScattered K → AdmissibleCodomain 𝕜 X →
    ∀ T : CZero 𝕜 K →L[𝕜] X, ¬ IsCompactOperator T →
      IsLUB (factorizationValues 𝕜 K X T) (dualEssentialNorm T)

end ScatteredSpaces

section Ordinals

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **Theorem 1.3** (page 3).

"Let α be an ordinal. Then any homomorphism from B(C([0,α])) into a Banach algebra
is continuous."

Homomorphism means 𝕜-linear and multiplicative; continuity is the conclusion,
not part of the homomorphism type. Neither the target algebra nor the
homomorphism is required to be unital. The target may be noncommutative.
-/
def Theorem_1_3 (α : Ordinal.{u}) : Prop :=
  ∀ (A : Type v) [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A],
    ∀ φ : (OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) →ₙₐ[𝕜] A, Continuous φ

/-- **Corollary 1.4** (page 3).

"Let α be an ordinal. Then the algebra of operators B(C([0,α])) and the Calkin
algebra B(C([0,α]))/K(C([0,α])) admit a unique algebra norm."

Both algebras are included. 'Unique' means equivalence, and the competing norms
are not required to be complete.
-/
def Corollary_1_4 (α : Ordinal.{u}) : Prop :=
  HasUniqueAlgebraNorm 𝕜 (B := OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) ∧
    HasUniqueCalkinNorm 𝕜 (OrdinalC 𝕜 α)

end Ordinals

end JLMS
