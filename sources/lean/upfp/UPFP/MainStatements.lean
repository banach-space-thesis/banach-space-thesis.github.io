import ThesisCommon.Analysis.SequenceSpaces
import ThesisCommon.Analysis.Cotype

/-! Acuaviva, Preservation of primariness under ℓ₁-, c₀-, and ℓ∞-sums,
supplied archive. These definitions record the original propositions; their proofs are separate.
Section 1 shares one counter across theorems, corollaries and remarks:
the intervening Remark 1.4 explains the numbering 1.5 and 1.6 below.
-/
noncomputable section
universe u v
namespace UPFP
open ThesisCommon

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Theorem 1.1 (`th: main1`): UPFP passes to ℓ₁(X) if X is self-similar
for some p ∈ [1,∞] or c₀, OR X* has finite cotype. Also ℓ₁(X) is primary.
The Banach dual, not X, occurs in the cotype hypothesis. -/
def Theorem_1_1 [CompleteSpace X] : Prop :=
  HasUPFP 𝕜 X →
    (IsSequenceSelfSimilar 𝕜 X ∨ HasFiniteCotype (X →L[𝕜] 𝕜)) →
    HasUPFP 𝕜 (EllOneSum ℕ X) ∧ IsPrimary 𝕜 (EllOneSum ℕ X)

/-- Theorem 1.2 (`th: main2`): UPFP passes to both c₀(X) and ℓ∞(X)
if X ≃ ℓp(X) for a finite p ≥ 1, OR X has finite cotype. Both are primary.
The self-similarity branch excludes p = ∞ and excludes c₀ self-similarity. -/
def Theorem_1_2 [CompleteSpace X] : Prop :=
  HasUPFP 𝕜 X →
    (IsFiniteLpSelfSimilar 𝕜 X ∨ HasFiniteCotype X) →
    (HasUPFP 𝕜 (CZeroSum X) ∧ HasUPFP 𝕜 (EllInfinitySum X)) ∧
    (IsPrimary 𝕜 (CZeroSum X) ∧ IsPrimary 𝕜 (EllInfinitySum X))

/-- Corollary 1.3 (unlabelled first corollary in Introduction): ℓ∞(Lp[0,1])
for every finite p ≥ 1, and c₀(L₁[0,1]), have UPFP and are primary. -/
def Corollary_1_3 : Prop :=
  (∀ p : BanachExponent, p.val ≠ ⊤ →
    HasUPFP 𝕜 (EllInfinitySum (IntervalLp 𝕜 p)) ∧
    IsPrimary 𝕜 (EllInfinitySum (IntervalLp 𝕜 p))) ∧
  (HasUPFP 𝕜 (CZeroSum (IntervalLp 𝕜 ⟨1, le_rfl⟩)) ∧
    IsPrimary 𝕜 (CZeroSum (IntervalLp 𝕜 ⟨1, le_rfl⟩)))

/-- Corollary 1.5 (unlabelled ordinal corollary in Introduction): for every
ordinal α, ℓ₁(C([0,α])) has UPFP and is primary, including exceptional
Alspach--Benyamini ordinals. There is no regularity restriction on α. -/
def Corollary_1_5 (α : Ordinal.{u}) : Prop :=
  HasUPFP 𝕜 (EllOneSum ℕ (OrdinalContinuous 𝕜 α)) ∧
  IsPrimary 𝕜 (EllOneSum ℕ (OrdinalContinuous 𝕜 α))

/-- Theorem 1.6 (`th:main3`): for every set Γ, ℓ₁(Γ,L₁[0,1]) has UPFP;
consequently C[0,1]* has UPFP and is primary. Γ is an arbitrary type,
with no cardinality, countability or nonemptiness assumption. -/
def Theorem_1_6 (Γ : Type u) : Prop :=
  HasUPFP 𝕜 (EllOneSum Γ (IntervalLp 𝕜 ⟨1, le_rfl⟩)) ∧
  (HasUPFP 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜) ∧
    IsPrimary 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜))

end UPFP

