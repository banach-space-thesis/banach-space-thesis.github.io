import Posets.MainStatements
import Posets.Matrices
import Posets.SeparableLimits
import PosetsCommon.MultiplicativeSection

/-! Exact additional paper targets currently expressible in the implemented
vocabulary. The inventory explicitly lists the remaining target declarations. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜]

/-- Corollary 3.3, AS PRINTED. Its empty-space counterexample is also checked. -/
def Corollary_3_3_printed : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K],
    HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))

/-- The usual nonempty-K convention, confirmed by the author. -/
def Corollary_3_3 : Prop :=
  ∀ (K : Type) [MetricSpace K] [CompactSpace K] [Nonempty K],
    HasUniqueMaximalClosedIdeal 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))

/-- Lemma 4.3, s-countable: closed subspaces, with both implications. -/
def Lemma_4_3 (𝒜 : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → ∀ X : Submodule 𝕜 (Space 𝕜 𝒜), IsClosed (X : Set (Space 𝕜 𝒜)) →
    (TopologicalSpace.SeparableSpace X ↔
      (familySupportSet 𝕜 (X : Set (Space 𝕜 𝒜))).Countable)

/-- Lemma 4.4, countable-to-fact-c0. Closedness of the containing c₀ copy is
retained, and ≃L means isomorphic, not isometric. -/
def Lemma_4_4 (𝒜 : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → ∀ X : Submodule 𝕜 (Space 𝕜 𝒜),
    TopologicalSpace.SeparableSpace X →
    ∃ Y : Submodule 𝕜 (Space 𝕜 𝒜), X ≤ Y ∧ IsClosed (Y : Set (Space 𝕜 𝒜)) ∧
      Nonempty (Y ≃L[𝕜] cZero 𝕜)

/-- The natural point inclusion in Lemma 4.8. -/
def pointInclusion {𝒜 ℬ : Set (Set ℕ)} (h : 𝒜 ⊆ ℬ) : Mrowka 𝒜 → Mrowka ℬ
  | .inl n => .inl n
  | .inr A => .inr ⟨A.val, h A.property⟩

def Lemma_4_8 (𝒜 ℬ : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → IsAlmostDisjoint ℬ → ∀ h : 𝒜 ⊆ ℬ,
    Topology.IsOpenEmbedding (pointInclusion h)

/-- Remark 4.9's canonical embedding, with the exact extension-by-zero formula.
This target does NOT assume the desired bounded extension exists. -/
def CanonicalEmbeddingExists (𝒜 ℬ : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → IsAlmostDisjoint ℬ → 𝒜 ⊆ ℬ →
  ∃ ι : BoundedHom 𝕜 (Space 𝕜 𝒜) (Space 𝕜 ℬ), Isometry ι ∧
    (∀ f n, ι f (Sum.inl n) = f (Sum.inl n)) ∧
    (∀ f (B : ℬ), ι f (Sum.inr B) =
      if h : B.val ∈ 𝒜 then f (Sum.inr ⟨B.val, h⟩) else 0)

def Corollary_4_10 (𝒜 : Set (Set ℕ)) (B : Set ℕ) : Prop :=
  IsAlmostDisjoint 𝒜 → B.Infinite → B ∉ 𝒜 → IsAlmostDisjoint (insert B 𝒜) →
    ∀ f : Space 𝕜 𝒜, Tendsto (fun k => f (Sum.inl k)) (Along B) (𝓝 0)

/-- Both Admission and Monotonicity in Lemma 4.15. Finite unions are literal. -/
def Lemma_4_15 (𝒜 ℬ : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Prop :=
  (∀ A ∈ 𝒜, A.Infinite) → (∀ B ∈ ℬ, B.Infinite) →
  HasBoundedRows 𝕜 M → Accepts 𝕜 𝒜 ℬ M →
  ((∀ B ∈ ℬ, ¬ Undermines 𝕜 B M) → Admits 𝕜 𝒜 ℬ M) ∧
  (∀ C D : Set ℕ, C.Infinite → D.Infinite →
    (∃ F : Finset (Set ℕ), (∀ A ∈ F, A ∈ 𝒜) ∧ C ⊆ ⋃ A ∈ F, A) →
    (∃ G : Finset (Set ℕ), (∀ B ∈ G, B ∈ ℬ) ∧ D ⊆ ⋃ B ∈ G, B) →
    AcceptsPair 𝕜 C D M)

/-- A separately exposed analytic obligation implicit in the reduced-matrix
definition: summable rows, the uniform bound, and the quantitative estimate. -/
def ReducedMatrixBound (𝒜 ℬ : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → IsAlmostDisjoint ℬ →
  ∀ T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ,
    HasBoundedRows 𝕜 (reducedMatrix 𝕜 T) ∧ matrixNorm 𝕜 (reducedMatrix 𝕜 T) ≤ ‖T‖

/-- 1_U is specified by its actual point values; membership in C₀ is part of
the existential statement, not an unproved constructor or axiom. -/
def IsNeighborhoodIndicator {𝒜 : Set (Set ℕ)} (A : 𝒜) (f : Space 𝕜 𝒜) : Prop :=
  (∀ n, f (Sum.inl n) = indicator 𝕜 A.val n) ∧
  ∀ B : 𝒜, f (Sum.inr B) = if B = A then 1 else 0

def Lemma_4_18 (𝒜 ℬ : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint 𝒜 → IsAlmostDisjoint ℬ →
  ∀ T : Space 𝕜 𝒜 →L[𝕜] Space 𝕜 ℬ,
    (∃ 𝒜' : Set (Set ℕ), 𝒜' ⊆ 𝒜 ∧ 𝒜'.Countable ∧
      (∀ (A : 𝒜), A.val ∉ 𝒜' → ∃ f : Space 𝕜 𝒜,
        IsNeighborhoodIndicator 𝕜 A f ∧
        ∀ k, T f (Sum.inl k) = matrixAction 𝕜 (reducedMatrix 𝕜 T) (indicator 𝕜 A.val) k) ∧
      (∀ A ∈ 𝒜 \ 𝒜', ∀ B ∈ ℬ, ¬ Rejects 𝕜 A B (reducedMatrix 𝕜 T))) ∧
    ((∃ 𝒜' ℬ' : Set (Set ℕ), 𝒜' ⊆ 𝒜 ∧ ℬ' ⊆ ℬ ∧ 𝒜'.Countable ∧ ℬ'.Countable ∧
      Admits 𝕜 (𝒜 \ 𝒜') (ℬ \ ℬ') (reducedMatrix 𝕜 T)) → FactorsThroughCZero 𝕜 T)

/-- Characteristic functions in Cantor space, with Bool's discrete topology. -/
def cantorCode (A : Set ℕ) : ℕ → Bool := fun n => decide (n ∈ A)

def Lemma_5_1 : Prop :=
  ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧ ¬ 𝒜.Countable ∧ IsClosed (cantorCode '' 𝒜)

/-- Full acceptance/rejection dichotomy: the pairs of original sets are
pairwise disjoint AS PAIRS OF FAMILY MEMBERS, not as subsets of ℕ.
The printed statement allows the two members within one pair to coincide. -/
def Lemma_5_2 (𝒜 : Set (Set ℕ)) (M : ScalarMatrix 𝕜) : Prop :=
  IsAlmostDisjoint 𝒜 → ¬ 𝒜.Countable →
  @MeasurableSet (ℕ → Bool) (borel (ℕ → Bool)) (cantorCode '' 𝒜) → HasBoundedRows 𝕜 M →
  (∃ 𝒜' : Set (Set ℕ), 𝒜' ⊆ 𝒜 ∧ 𝒜'.Countable ∧ ∃ a : 𝕜,
    Accepts 𝕜 (𝒜 \ 𝒜') (𝒜 \ 𝒜') (M - a • identityMatrix 𝕜)) ∨
  (∃ A A' B : Set ℕ → Set ℕ,
    (∀ ξ, A ξ ∈ 𝒜 ∧ A' ξ ∈ 𝒜 ∧ (B ξ).Infinite ∧
      B ξ ⊆ A ξ ∪ A' ξ ∧ Rejects 𝕜 (B ξ) (B ξ) M) ∧
    Pairwise (fun ξ η => Disjoint ({A ξ, A' ξ} : Set (Set ℕ)) {A η, A' η}))

/-- Corollary 8.6: exactly 2^continuum maximal closed ideals. -/
def Corollary_8_6 : Prop :=
  ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
    Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃ Set (Set ℕ))

/-- Lemma 6.20. Kernel equality is a hypothesis about an actual ideal, not
an axiom. The checked common theorem supplies its full proof. -/
def Lemma_6_20 {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] [Module 𝕜 A] [Module 𝕜 B]
    (θ : A →ₗ[𝕜] B) (I : TwoSidedIdeal A) : Prop :=
  (∀ x, θ x = 0 ↔ x ∈ I) →
  (∃ ρ : B → A, (∀ a b, ρ (a * b) = ρ a * ρ b) ∧ Function.RightInverse ρ θ) →
  IsMultiplicative 𝕜 θ

theorem lemma_6_20_proof {A B : Type*} [NonUnitalRing A] [NonUnitalRing B] [Module 𝕜 A] [Module 𝕜 B]
    (θ : A →ₗ[𝕜] B) (I : TwoSidedIdeal A) : Lemma_6_20 𝕜 θ I := by
  rintro hker ⟨ρ, hρ, hsection⟩
  exact multiplicative_of_section θ I hker ρ hρ hsection

end Posets
