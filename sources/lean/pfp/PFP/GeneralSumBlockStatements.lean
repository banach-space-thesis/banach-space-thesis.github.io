import PFP.GeneralSumStatements
import ThesisCommon.Analysis.CoordinateMaskSubspaces

/-! Section 4.24--4.30 specifications on actual supported coordinate spaces.
These are targets, not proofs. The context-restored 4.27 and 4.30 explicitly
require the uncountable regime described at the start of Section 4; separate
`_asPrinted` formulas preserve the omitted-premise versions verbatim.
-/
noncomputable section
open scoped Cardinal ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon TopologicalSpace
universe u v w
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)
  (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The ordinal index α<|Γ|, using the initial ordinal of the actual cardinal. -/
abbrev CoordinateBlockIndex := (Cardinal.mk Γ).ord.toType

def IsCountableCoordinatePartition (B : CoordinateBlockIndex Γ → Set Γ) : Prop :=
  Pairwise (fun α β => Disjoint (B α) (B β)) ∧
    (∀ α, (B α).Countable) ∧ (⋃ α, B α) = Set.univ

/-- The three exact block-decomposition conclusions. Q is the actual
compression on the supported subspace, not an independently chosen operator. -/
def EllOneTriangularBlockDecomposition
    (P : EllOneSum Γ X →L[𝕜] EllOneSum Γ X)
    (B : CoordinateBlockIndex Γ → Set Γ) : Prop :=
  IsCountableCoordinatePartition Γ B ∧
  (∀ α, ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) 1 (B α),
    ∀ γ ∉ ⋃ β ≤ α, B β, P x γ = 0) ∧
  (∀ α, (lpBlockCompression 1 P (B α)).comp (lpBlockCompression 1 P (B α)) =
    lpBlockCompression 1 P (B α)) ∧
  (∀ α, {β : CoordinateBlockIndex Γ | β < α ∧
    ((lpCoordinateProjection (𝕜 := 𝕜) 1 (B β)).comp P).comp
      (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) 1 (B α)).subtypeL ≠ 0}.Countable)

/-- Lemma 4.24. Empty blocks remain allowed, exactly as in the assertion. -/
def Lemma_4_24 [CompleteSpace X] : Prop :=
  IsWeaklyCompactlyGenerated 𝕜 X →
    ∀ P : EllOneSum Γ X →L[𝕜] EllOneSum Γ X, P.comp P = P →
      ∃ B : CoordinateBlockIndex Γ → Set Γ, EllOneTriangularBlockDecomposition 𝕜 Γ X P B

/-- Lemma 4.25, including its all-vector assertion on W, represented by
the actual coordinate subspace supported on the union of the selected blocks. -/
def Lemma_4_25 [CompleteSpace X] : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → IsWeaklyCompactlyGenerated 𝕜 X →
    ∀ P : EllOneSum Γ X →L[𝕜] EllOneSum Γ X, P.comp P = P →
      ∀ B : CoordinateBlockIndex Γ → Set Γ, EllOneTriangularBlockDecomposition 𝕜 Γ X P B →
        ∃ H : Set (CoordinateBlockIndex Γ), Cardinal.mk H = Cardinal.mk Γ ∧
          (∀ α ∈ H, ∀ β ∈ H, α ≠ β →
            ((lpCoordinateProjection (𝕜 := 𝕜) 1 (B β)).comp P).comp
              (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) 1 (B α)).subtypeL = 0) ∧
          (∀ z : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) 1 (⋃ α ∈ H, B α),
            ∀ α ∈ H, lpCoordinateProjection (𝕜 := 𝕜) 1 (B α) (P z) =
              lpCoordinateProjection (𝕜 := 𝕜) 1 (B α)
                (P (lpCoordinateProjection (𝕜 := 𝕜) 1 (B α) z)))

def LpLargeDiagonalBlocks (p : BanachExponent)
    (P : lp (fun _ : Γ => X) p.val →L[𝕜] lp (fun _ : Γ => X) p.val) : Prop :=
  ∃ B : CoordinateBlockIndex Γ → Set Γ, IsCountableCoordinatePartition Γ B ∧
    (∀ α, (lpBlockCompression p.val P (B α)).comp (lpBlockCompression p.val P (B α)) =
      lpBlockCompression p.val P (B α)) ∧
    ∃ H : Set (CoordinateBlockIndex Γ), Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
        ((lpCoordinateProjection (𝕜 := 𝕜) p.val (B β)).comp P).comp
          (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p.val (B α)).subtypeL = 0

def CZeroLargeDiagonalBlocks [TopologicalSpace Γ] [DiscreteTopology Γ]
    (P : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) : Prop :=
  ∃ B : CoordinateBlockIndex Γ → Set Γ, IsCountableCoordinatePartition Γ B ∧
    (∀ α, (cZeroBlockCompression P (B α)).comp (cZeroBlockCompression P (B α)) =
      cZeroBlockCompression P (B α)) ∧
    ∃ H : Set (CoordinateBlockIndex Γ), Cardinal.mk H = Cardinal.mk Γ ∧
      ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
        ((cZeroCoordinateProjection (𝕜 := 𝕜) (B β)).comp P).comp
          (cZeroSupportedSubmodule (𝕜 := 𝕜) (X := X) (B α)).subtypeL = 0

/-- Both alternatives of Lemma 4.26 as printed, without adding a cardinal premise. -/
def Lemma_4_26_asPrinted [TopologicalSpace Γ] [DiscreteTopology Γ] [CompleteSpace X] : Prop :=
  SeparableSpace X →
    (∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
      ∀ P : lp (fun _ : Γ => X) p.val →L[𝕜] lp (fun _ : Γ => X) p.val,
        P.comp P = P → LpLargeDiagonalBlocks 𝕜 Γ X p P) ∧
    (∀ P : C₀(Γ, X) →L[𝕜] C₀(Γ, X), P.comp P = P → CZeroLargeDiagonalBlocks 𝕜 Γ X P)

/-- Lemma 4.26 in the section's uncountable regime. -/
def Lemma_4_26 [TopologicalSpace Γ] [DiscreteTopology Γ] [CompleteSpace X] : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → Lemma_4_26_asPrinted 𝕜 Γ X

/-- Lemma 4.28 is specifically the actual ℓ₁ sum, even though it occurs
between two general symmetric-sum statements. -/
def Lemma_4_28 [CompleteSpace X] : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → IsWeaklyCompactlyGenerated 𝕜 X →
    ∀ T : EllOneSum Γ X →L[𝕜] EllOneSum Γ X,
      ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
        ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
          ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
            (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) = 0

variable (E : Type w) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The actual coordinate entry R_β T R_α as an operator on the whole sum. -/
def generalCoordinateEntry (b : NormalizedSchauderFamily 𝕜 Γ E) (hb : b.IsOneUnconditional)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X :=
  ((UncountableSchauderSum.coordinateProjection {β}).comp T).comp
    (UncountableSchauderSum.coordinateProjection {α})

/-- Exact printed alternatives of 4.27. In (a), the one-sided choice may
depend on γ. The missing uncountability premise in (b) is deliberately retained. -/
def Lemma_4_27_asPrinted [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm,
    ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      ((Cardinal.aleph 1 < Cardinal.mk Γ ∧ ∀ γ,
        {η | generalCoordinateEntry 𝕜 Γ X E b hs.1 T η γ ≠ 0}.Countable ∨
        {η | generalCoordinateEntry 𝕜 Γ X E b hs.1 T γ η ≠ 0}.Countable) ∨
      (∀ γ, {η | generalCoordinateEntry 𝕜 Γ X E b hs.1 T η γ ≠ 0}.Countable ∧
        {η | generalCoordinateEntry 𝕜 Γ X E b hs.1 T γ η ≠ 0}.Countable)) →
      ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
        ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → generalCoordinateEntry 𝕜 Γ X E b hs.1 T β α = 0

/-- Context-restored Lemma 4.27; the unrestricted printed formula above
is not asserted to be true for countable Γ. -/
def Lemma_4_27 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → Lemma_4_27_asPrinted 𝕜 Γ X E b

def Lemma_4_29 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → ∀ hs : b.HasSymmetricNorm,
    ¬ b.EquivalentEllOne → HasCountableTotalDual 𝕜 X →
      ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
        ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
          ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → generalCoordinateEntry 𝕜 Γ X E b hs.1 T β α = 0

/-- Printed 4.30, preserving its omitted cardinal premise for inspection. -/
def Lemma_4_30_asPrinted [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  ∀ hs : b.HasSymmetricNorm, ¬ b.EquivalentEllOne → SeparableSpace X →
    ∀ T : UncountableSchauderSum b hs.1 X →L[𝕜] UncountableSchauderSum b hs.1 X,
      ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
        ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β → generalCoordinateEntry 𝕜 Γ X E b hs.1 T β α = 0

/-- Lemma 4.30 with the uncountable regime from the section opening restored. -/
def Lemma_4_30 [CompleteSpace X] (b : NormalizedSchauderFamily 𝕜 Γ E) : Prop :=
  Cardinal.aleph0 < Cardinal.mk Γ → Lemma_4_30_asPrinted 𝕜 Γ X E b

end PFP
