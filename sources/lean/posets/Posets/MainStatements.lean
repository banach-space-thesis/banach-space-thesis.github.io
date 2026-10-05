import Posets.Models
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Metrizable.Basic

/-! Section 1 targets. Every declaration below is a proposition definition,
not a proof. Source labels identify the authoritative uploaded version.
Universe Type is used for the concrete families; P may live in any universe. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
open scoped ZeroAtInfty
open ThesisCommon
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- Theorem 1.1, th: almost-disjoint-families-few-operators.
An order embedding into P(continuum), NOT a cardinal bound by continuum.
Both factorisation clauses, multiplicativity, isometry, identities and coherence
are included. The family and maps may depend on the chosen scalar field. -/
def Theorem_1_1 (P : Type*) [PartialOrder P] : Prop :=
  Nonempty (P ↪o Set (Set ℕ)) →
  ∃ 𝒜 : P → Set (Set ℕ),
    (∀ t, IsAlmostDisjoint (𝒜 t) ∧ ¬ (𝒜 t).Countable) ∧
    ∃ ι : ∀ s t, s ≤ t → BoundedHom 𝕜 (Space 𝕜 (𝒜 s)) (Space 𝕜 (𝒜 t)),
      (∀ s t h, Isometry (ι s t h)) ∧
      (∀ s, (ι s s le_rfl).toContinuousLinearMap = ContinuousLinearMap.id 𝕜 _) ∧
      (∀ r s t hrs hst,
        (ι s t hst).toContinuousLinearMap.comp (ι r s hrs).toContinuousLinearMap =
          (ι r t (hrs.trans hst)).toContinuousLinearMap) ∧
      (∀ s t h, ∀ T : Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        ∃ a : 𝕜, ∃ S : Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
          FactorsThroughCZero 𝕜 S ∧ T = a • (ι s t h).toContinuousLinearMap + S) ∧
      (∀ s t, ¬ s ≤ t → ∀ T : Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        FactorsThroughCZero 𝕜 T)

/-- Corollary 1.2. Indexing by P(P(ℕ)) retains 2^continuum distinct spaces;
each family is required to have exactly continuum members. -/
def Corollary_1_2 : Prop :=
  ∃ 𝒜 : Set (Set ℕ) → Set (Set ℕ),
    (∀ t, IsAlmostDisjoint (𝒜 t) ∧ JFA.HasContinuumSize (𝒜 t)) ∧
    ∀ s t, s ≠ t → ¬ Nonempty (Space 𝕜 (𝒜 s) ≃L[𝕜] Space 𝕜 (𝒜 t))

/-- Proposition 1.3, prop: quotient-to-ideals. An order isomorphism determines
the lattice isomorphism. Its underlying map must be the printed inverse image. -/
def Proposition_1_3 (𝒜 : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 →
  let E := Space 𝕜 𝒜
  let K : Set (E →L[𝕜] E) := {T | IsCompactOperator T}
  IsClosedIdeal 𝕜 K ∧ K ≠ {0} ∧
  (∀ I, IsClosedIdeal 𝕜 I → I ≠ {0} → K ⊆ I) ∧
  ∃ e : QuotientClosedIdeals 𝕜 E ≃o IdealsAboveCompact 𝕜 E,
    ∀ I, (e I).val = (quotientMap 𝕜 E) ⁻¹' I.val

/-- Theorem 1.5, th: quotient-algebras (Remark 1.4 consumes a number).
The product is dependent ℓ∞ with its actual norm. Zero products are allowed;
the θ norm clause applies only to a nonzero product. -/
def Theorem_1_5 (C : ℕ → Type) [∀ n, NormedRing (C n)]
    [∀ n, NormedAlgebra 𝕜 (C n)] [∀ n, CompleteSpace (C n)] : Prop :=
  (∀ n, AdmissibleAlgebra 𝕜 (C n)) →
  ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
    ∃ θ : BoundedHom 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) (NormedProduct C),
    ∃ ρ : BoundedHom 𝕜 (NormedProduct C) (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜),
      StrongSplit 𝕜 (Space 𝕜 𝒜) (NormedProduct C) θ ρ ∧ Isometry ρ ∧
      (Nontrivial (NormedProduct C) → ‖θ.toContinuousLinearMap‖ = 1)

/-- Corollary 1.7 (Remark 1.6 consumes a number). The quotient is the actual
normed vector quotient; multiplication is tested on arbitrary representatives. -/
def Corollary_1_7 (C : Type) [Ring C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] [IsSemisimpleRing C] : Prop :=
  ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
    ∃ e : SeparableQuotient ℂ (Space ℂ 𝒜) ≃ₗ[ℂ] C,
      ∀ S T : Space ℂ 𝒜 →L[ℂ] Space ℂ 𝒜, e (quotientMap ℂ (Space ℂ 𝒜) (S * T)) =
        e (quotientMap ℂ (Space ℂ 𝒜) S) * e (quotientMap ℂ (Space ℂ 𝒜) T)

/-- Theorem 1.8, th:zfc-discontinuous-homomorphism. Range equality with the
upper triangular subset is precisely surjectivity onto T₂. The latter has its
finite-dimensional subspace topology, so continuity into ambient matrices is
equivalent to continuity into T₂. Both conclusions, including K'''=∅, occur. -/
def Theorem_1_8 : Prop :=
  (∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
    ∃ Ψ : (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) →ₗ[𝕜] Matrix (Fin 2) (Fin 2) 𝕜,
      IsMultiplicative 𝕜 Ψ ∧ Set.range Ψ = triangularTwo 𝕜 ∧ ¬ Continuous Ψ) ∧
  (∃ (K : Type) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K),
    derivedSet (derivedSet (derivedSet (Set.univ : Set K))) = ∅ ∧
    ∃ Ψ : (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) →ₗ[𝕜] Matrix (Fin 2) (Fin 2) 𝕜,
      IsMultiplicative 𝕜 Ψ ∧ Set.range Ψ = triangularTwo 𝕜 ∧ ¬ Continuous Ψ)

/-- The uniform final clause of Proposition 1.10: one n works for EVERY K.
Exactly n uses an actual bijection, not Nat.card (which is 0 for infinite types). -/
def MissingSeparableIdealCount : Prop :=
  ∃ n : ℕ, (n = 2 ∨ n = 3) ∧
    ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K],
      TopologicalSpace.SeparableSpace C(K, 𝕜) →
      ¬ Nonempty (NontrivialClosedIdeals 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜)) ≃ Fin n)

/-- Proposition 1.10, prop:separable, AS PRINTED, including empty K.
The first clause is false for K=∅; see Counterexamples.lean. -/
def Proposition_1_10_printed : Prop :=
  (∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K],
    TopologicalSpace.SeparableSpace C(K, 𝕜) →
      HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))) ∧
    MissingSeparableIdealCount 𝕜

/-- Proposition 1.10 with the usual nonempty-space convention made explicit.
The author confirmed this interpretation on 1 October 2026. -/
def Proposition_1_10 : Prop :=
  (∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K],
    TopologicalSpace.SeparableSpace C(K, 𝕜) →
      HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))) ∧
    MissingSeparableIdealCount 𝕜

end Posets
