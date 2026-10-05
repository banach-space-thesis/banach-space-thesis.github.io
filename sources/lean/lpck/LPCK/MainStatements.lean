import ThesisCommon.Analysis.SequenceSpaces

/-! Acuaviva, Primariness of the spaces ℓp(C(K)), supplied v2 archive.
All three declarations below are OPEN TARGETS, not theorems.
The exponent subtype carries precisely 1 ≤ p ≤ ∞.
-/
noncomputable section
universe u
namespace LPCK
open ThesisCommon

/-- Theorem 1.1 (`th: main-theorem`, Introduction): for every ordinal α
and 1 ≤ p ≤ ∞, ℓp(C([0,α])) has UPFP and is primary. Both clauses are retained.
The ordinal universe is arbitrary. Scalars may be real or complex. -/
def Theorem_1_1 (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u})
    (p : BanachExponent) : Prop :=
  HasUPFP 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α)) ∧
  IsPrimary 𝕜 (SequenceSum p (OrdinalContinuous 𝕜 α))

/-- Theorem 1.2 (`th: main-theorem2`, Introduction): ℓp(C[0,1]) has UPFP
for every 1 ≤ p ≤ ∞. Its stated conclusion is UPFP; primariness is also
discussed in the proof and included in Corollary 1.3. -/
def Theorem_1_2 (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) : Prop :=
  HasUPFP 𝕜 (SequenceSum p (IntervalContinuous 𝕜))

/-- Corollary 1.3 (`cor: compact-metric-primary`, Introduction): for every
compact metric K and 1 ≤ p ≤ ∞, ℓp(C(K)) is primary. Empty and finite K are
allowed; no separability or infinitude assumption is added. -/
def Corollary_1_3 (𝕜 : Type*) [RCLike 𝕜] (K : Type u)
    [MetricSpace K] [CompactSpace K] (p : BanachExponent) : Prop :=
  IsPrimary 𝕜 (SequenceSum p C(K, 𝕜))

end LPCK
