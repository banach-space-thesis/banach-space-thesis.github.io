import PFP.UncountableStatements
import ThesisCommon.Analysis.UncountableSchauderSumSupport
import ThesisCommon.Analysis.CountableTotalDual

/-! Full arbitrary-index symmetric-sum specifications from Section 4.
Every sum below is the actual norm-series space, with its proved norm,
coordinates, and completeness. These Prop declarations assert no proofs.
As in the source's direct-sum conventions, the scalar basis is normalized
and the selected symmetric norm is one-unconditional.
-/
noncomputable section
open scoped Cardinal ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon TopologicalSpace
universe u v w
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)
  (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (X : Type w) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- Uniform and cofinality alternatives, including the PFP consequence in
the uniform case. The index set determines the cofinality condition. -/
def FactorisationTransfer (Z : Type*) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] : Prop :=
  (HasUPFP 𝕜 X → HasPFP 𝕜 Z ∧ HasUPFP 𝕜 Z) ∧
    (HasPFP 𝕜 X → HasUncountableCofinality Γ → HasPFP 𝕜 Z)

/-- Theorem 4.3(ii): arbitrary uncountable Γ and separable coefficient X. -/
def Theorem_4_3_ii [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → ∀ hs : b.HasSymmetricNorm,
    ¬ b.EquivalentEllOne → SeparableSpace X →
      FactorisationTransfer 𝕜 Γ X (UncountableSchauderSum b hs.1 X)

/-- Theorem 4.3(iii): a countable total dual set, with the strictly larger
than aleph_1 cardinal restriction retained. -/
def Theorem_4_3_iii [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → ∀ hs : b.HasSymmetricNorm,
    ¬ b.EquivalentEllOne → HasCountableTotalDual 𝕜 X →
      FactorisationTransfer 𝕜 Γ X (UncountableSchauderSum b hs.1 X)

/-- All three clauses of the original Theorem 4.3. -/
def Theorem_4_3 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Theorem_4_3_i 𝕜 Γ X ∧ Theorem_4_3_ii 𝕜 Γ E X b ∧ Theorem_4_3_iii 𝕜 Γ E X b

/-- The general symmetric-sum assertion of Corollary 4.9. -/
def Corollary_4_9_general [CompleteSpace X]
    (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → ∀ hs : b.HasSymmetricNorm,
    ¬ b.EquivalentEllOne → SeparableSpace X → HasUPFP 𝕜 X →
      HasUPFP 𝕜 (UncountableSchauderSum b hs.1 X)

/-- The two concrete consequences of Corollary 4.9 are independent of any
separately supplied scalar basis. -/
def Corollary_4_9_concrete [CompleteSpace X] [TopologicalSpace Γ] [DiscreteTopology Γ] : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → SeparableSpace X → HasUPFP 𝕜 X →
    (∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
      HasUPFP 𝕜 (lp (fun _ : Γ => X) p.val)) ∧ HasUPFP 𝕜 C₀(Γ, X)

/-- Full Corollary 4.9, including both concrete sequence-space consequences.
The discrete topology is used only to express the actual c₀(Γ,X) space. -/
def Corollary_4_9 [CompleteSpace X] [TopologicalSpace Γ] [DiscreteTopology Γ]
    (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Corollary_4_9_general 𝕜 Γ E X b ∧ Corollary_4_9_concrete 𝕜 Γ X

/-- Lemma 4.12 on the full norm-series sum, with no countability assumption
on the index set. -/
def Lemma_4_12 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, ∀ x : UncountableSchauderSum b hs.1 X,
    (Function.support (fun γ => x γ)).Countable

/-- Lemma 4.13: any norm-separable subset is contained in an actual
countable-coordinate subspace. -/
def Lemma_4_13 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, ∀ Y : Set (UncountableSchauderSum b hs.1 X),
    IsSeparable Y → ∃ Δ : Set Γ, Δ.Countable ∧
      Y ⊆ (UncountableSchauderSum.supportedSubmodule (b := b) (hb := hs.1) (Y := X) Δ :
        Set (UncountableSchauderSum b hs.1 X))

/-- Lemma 4.14: scalar support reduction implies vector-valued support
reduction. The scalar assumption refers to actual coordinates in E. -/
def Lemma_4_14 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm,
    (∀ S : X →L[𝕜] E, ∃ Λ : Set Γ, Λ.Countable ∧
      ∀ x : X, ∀ γ ∉ Λ, b.coord γ (S x) = 0) →
    ∀ T : X →L[𝕜] UncountableSchauderSum b hs.1 X,
      ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0

/-- The common exact conclusion of the support-reduction results. -/
def PreservesCountableCoordinateSupports (b : NormalizedSchauderFamily 𝕜 Γ E)
    (hb : b.IsOneUnconditional)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X) : Prop :=
  ∀ Δ : Set Γ, Δ.Countable → ∃ Λ : Set Γ, Λ.Countable ∧
    ∀ x : UncountableSchauderSum b hb X,
      (∀ γ ∉ Δ, x γ = 0) → ∀ γ ∉ Λ, T x γ = 0

/-- Lemma 4.15, with the full separable-range hypothesis and countable
coordinate-block conclusion. -/
def Lemma_4_15 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm,
    (∀ S : X →L[𝕜] E, IsSeparable (Set.range S)) →
    ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      PreservesCountableCoordinateSupports 𝕜 Γ E X b hs.1 T

/-- The separable alternative of Corollary 4.16. -/
def Corollary_4_16_separable [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, SeparableSpace X →
    ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      PreservesCountableCoordinateSupports 𝕜 Γ E X b hs.1 T

/-- The WCG alternative of Corollary 4.16, on actual ℓ₁(Γ,X). -/
def Corollary_4_16_ellOne [CompleteSpace X] : Prop :=
  IsWeaklyCompactlyGenerated 𝕜 X →
    ∀ T : EllOneSum Γ X →L[𝕜] EllOneSum Γ X,
      ∀ Δ : Set Γ, Δ.Countable → ∃ Λ : Set Γ, Λ.Countable ∧
        ∀ x : EllOneSum Γ X, (∀ γ ∉ Δ, x γ = 0) → ∀ γ ∉ Λ, T x γ = 0

/-- Both alternatives of Corollary 4.16; the WCG alternative is asserted
only for ℓ₁, as in the manuscript. -/
def Corollary_4_16 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Corollary_4_16_separable 𝕜 Γ E X b ∧ Corollary_4_16_ellOne 𝕜 Γ X

/-- Lemma 4.17: each scalar functional sees at most countably many source
coordinates. R_{γ} is the actual singleton coordinate projection. -/
def Lemma_4_17 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, ¬ b.EquivalentEllOne →
    ∀ (φ : X →L[𝕜] 𝕜) (T : UncountableSchauderSum b hs.1 X →L[𝕜] X),
      ∃ Δ : Set Γ, Δ.Countable ∧ ∀ γ ∉ Δ,
        (φ.comp T).comp (UncountableSchauderSum.coordinateProjection {γ}) = 0

/-- Lemma 4.18: a countable total dual set gives countable incoming
coordinate support for every bounded operator into X. -/
def Lemma_4_18 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, ¬ b.EquivalentEllOne → HasCountableTotalDual 𝕜 X →
    ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] X,
      ∃ Δ : Set Γ, Δ.Countable ∧ ∀ γ ∉ Δ,
        T.comp (UncountableSchauderSum.coordinateProjection {γ}) = 0

end PFP
