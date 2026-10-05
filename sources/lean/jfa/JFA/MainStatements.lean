import JFA.Definitions

/-!
# Main results: statements only

Antonio Acuaviva, Operators on injective tensor products of separable Banach
spaces and spaces with few operators, JFA 290 (2026), 111203.
https://doi.org/10.1016/j.jfa.2025.111203

Numbering and wording checked against the local JFA v2 manuscript, pp. 2-4,
and sample-draft/sources/tensor/1- Introduction and results.tex.

Every numbered declaration here is a definition of a proposition.
Theorem 1.1 is proved separately by JFA.theorem_1_1 in MainTheorem.lean.
Corollary 1.2 is proved by JFA.corollary_1_2 in TensorCancellation.lean.
Corollary 1.3 is proved by JFA.corollary_1_3 in CZeroTensor.lean.
Theorem 1.4 is proved by JFA.theorem_1_4 in ComplementedClassification.lean.
Theorem 1.6 is proved by JFA.theorem_1_6 in IdealClassification.lean.
There are no asserted paper results, no proof placeholders, and no new axioms.
The separate proof declarations establish these propositions; their semantic
agreement with the article remains available for human review.
-/

noncomputable section
open TopologicalSpace
open scoped TensorProduct ZeroAtInfty
namespace JFA
universe u

section TensorResults
variable (𝕜 : Type u) [RCLike 𝕜]
variable (E F X : Type u)
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Theorem 1.1.** Let E,F be separable Banach spaces and X a nonseparable
Banach space with few operators. Every T : E ⊗̂_α X → F ⊗̂_ε X has a UNIQUE
decomposition T = U ⊗̂ I + S, with S of separable range.

A,ι range over completions of the assigned α-norm. The equation is imposed on
all elementary tensors; by continuity and density this is precisely the operator
equation. In particular T-S itself supplies the bounded extension U ⊗̂ I.
Existential uniqueness is on the PAIR (U,S), not just on one component. -/
def Theorem_1_1 [CompleteSpace E] [CompleteSpace F] [CompleteSpace X] : Prop :=
  SeparableSpace E → SeparableSpace F → ¬ SeparableSpace X → HasFewOperators 𝕜 X →
    ∀ α : UniformCrossnorm 𝕜,
    ∀ (A : Type u) [NormedAddCommGroup A] [NormedSpace 𝕜 A] [CompleteSpace A],
    ∀ ι : E ⊗[𝕜] X →ₗ[𝕜] A, IsTensorCompletion 𝕜 E X A (α.normFor E X) ι →
    ∀ T : A →L[𝕜] InjectiveTensor 𝕜 F X,
    ∃! d : (E →L[𝕜] F) × (A →L[𝕜] InjectiveTensor 𝕜 F X),
      HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) d.2 ∧
      ∀ e x, T (ι (e ⊗ₜ[𝕜] x)) =
        injectivePure 𝕜 F X (d.1 e) x + d.2 (ι (e ⊗ₜ[𝕜] x))

/-- **Corollary 1.2.** Under the same separability and few-operator hypotheses,
E ⊗̂_ε X is isomorphic to F ⊗̂_ε X if and only if E is isomorphic to F.
Both sides refer to bounded linear isomorphisms, not isometries. -/
def Corollary_1_2 [CompleteSpace E] [CompleteSpace F] [CompleteSpace X] : Prop :=
  SeparableSpace E → SeparableSpace F → ¬ SeparableSpace X → HasFewOperators 𝕜 X →
    (Isomorphic 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) ↔ Isomorphic 𝕜 E F)

end TensorResults

/-- **Corollary 1.3.** Let L be nonmetrizable, locally compact Hausdorff, with
C₀(L) admitting few operators, and let M₁,M₂ be compact metric spaces. Every
T : C₀(M₁ × L) → C₀(M₂ × L) has a UNIQUE representation U ⊗̂ I + S.

The tensor equation is written pointwise on the elementary functions
(m,l) ↦ f(m) g(l), using h as their actual C₀ representative. This avoids
assuming an unproved tensor/function-space identification as an extra hypothesis.
The hypothesis on L is exactly nonmetrizability, not nonseparability of L. -/
def Corollary_1_3 (𝕜 : Type*) [RCLike 𝕜]
    (L : Type*) [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]
    (M₁ M₂ : Type*) [MetricSpace M₁] [CompactSpace M₁]
    [MetricSpace M₂] [CompactSpace M₂] : Prop :=
  ¬ MetrizableSpace L → HasFewOperators 𝕜 C₀(L, 𝕜) →
    ∀ T : C₀(M₁ × L, 𝕜) →L[𝕜] C₀(M₂ × L, 𝕜),
    ∃! d : (C(M₁, 𝕜) →L[𝕜] C(M₂, 𝕜)) ×
        (C₀(M₁ × L, 𝕜) →L[𝕜] C₀(M₂ × L, 𝕜)),
      HasSeparableRange 𝕜 C₀(M₁ × L, 𝕜) C₀(M₂ × L, 𝕜) d.2 ∧
      ∀ (f : C(M₁, 𝕜)) (g : C₀(L, 𝕜)) (h : C₀(M₁ × L, 𝕜)),
        (∀ p, h p = f p.1 * g p.2) →
        ∀ p, T h p = d.1 f p.1 * g p.2 + d.2 h p

section Applications
variable (𝕜 : Type*) [RCLike 𝕜]
variable (𝒜 : Set (Set ℕ))

/-- **Theorem 1.4.** For an almost disjoint family of continuum cardinality
whose C₀(K_A) has few operators, every infinite-dimensional complemented
subspace of C₀(omega × K_A) is isomorphic to EXACTLY ONE of c₀, C₀(K_A)^n
(n positive), or the whole space. Uniqueness includes the finite exponent.
No finite-dimensional subspace is included in the assertion. -/
def Theorem_1_4 : Prop :=
  IsAlmostDisjoint 𝒜 → HasContinuumSize 𝒜 → HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜) →
    ∀ W : Submodule 𝕜 (AmplifiedMrowka 𝕜 𝒜),
      IsComplemented 𝕜 (AmplifiedMrowka 𝕜 𝒜) W → ¬ FiniteDimensional 𝕜 W →
        ∃! c : ComplementedModel,
          IsModel 𝕜 (MrowkaCZero 𝕜 𝒜) (AmplifiedMrowka 𝕜 𝒜) W c

/-- **Theorem 1.6.** Under the same hypotheses, the complete lattice of closed
two-sided operator ideals is
{0} < K(Y) < G_c₀(Y) = X(Y) < closure(G_C₀(K_A)(Y)) < B(Y).

All four inclusions are strict. The equivalence over arbitrary subsets I says
both that there are NO other closed ideals and that each listed set is one.
The factorization ideal G_c₀ has no closure; the penultimate ideal does. -/
def Theorem_1_6 : Prop :=
  IsAlmostDisjoint 𝒜 → HasContinuumSize 𝒜 → HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜) →
    let Y := AmplifiedMrowka 𝕜 𝒜
    let I₀ : Set (Y →L[𝕜] Y) := {0}
    let I₁ := compactOperators 𝕜 Y
    let I₂ := factorizationOperators 𝕜 Y (cZero 𝕜)
    let I₃ := closure (factorizationOperators 𝕜 Y (MrowkaCZero 𝕜 𝒜))
    I₀ ⊂ I₁ ∧ I₁ ⊂ I₂ ∧ I₂ = separableOperators 𝕜 Y ∧ I₂ ⊂ I₃ ∧ I₃ ⊂ Set.univ ∧
      ∀ I : Set (Y →L[𝕜] Y), IsClosedOperatorIdeal 𝕜 Y I ↔
        I = I₀ ∨ I = I₁ ∨ I = I₂ ∨ I = I₃ ∨ I = Set.univ

end Applications
end JFA
