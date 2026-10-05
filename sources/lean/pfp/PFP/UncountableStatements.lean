import PFP.MainStatements
import ThesisCommon.Analysis.UniformPrimariness
import Mathlib.SetTheory.Cardinal.Cofinality

/-! The exact standard-sum assertions of §4. No assertion here supplies a
proof. The uniformly-primary convention was selected by the user; every
cardinality/cofinality, WCG/separability and exponent condition remains explicit.
-/
noncomputable section
open scoped Cardinal ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon TopologicalSpace
universe u v w

/-- Cofinality of the cardinal |Γ|, computed from its initial ordinal. -/
def HasUncountableCofinality (Γ : Type u) : Prop := ℵ₀ < (Cardinal.mk Γ).ord.cof

/-- Both alternatives of Theorem 4.1, including primariness in the uniform case.
This is an open transfer statement, not an axiom or a typeclass instance. -/
def PrimarinessTransfer (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (Γ : Type u) : Prop :=
  (IsUniformlyPrimary 𝕜 X → IsPrimary 𝕜 Y ∧ IsUniformlyPrimary 𝕜 Y) ∧
  (IsPrimary 𝕜 X → HasUncountableCofinality Γ → IsPrimary 𝕜 Y)

/-- Full Theorem 4.1 (thm:A). Part (i) uses WCG and |Γ|>aleph_1;
part (ii) uses separability and mere uncountability, and excludes p=1,infinity.
c₀ is included explicitly. Γ has its discrete topology for the c₀ clause. -/
def Theorem_4_1 (𝕜 : Type*) [RCLike 𝕜]
    (Γ : Type u) [TopologicalSpace Γ] [DiscreteTopology Γ]
    (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : Prop :=
  (Cardinal.aleph 1 < Cardinal.mk Γ → IsWeaklyCompactlyGenerated 𝕜 X →
    PrimarinessTransfer 𝕜 (EllOneSum ℕ X) (EllOneSum Γ X) Γ) ∧
  (Cardinal.aleph0 < Cardinal.mk Γ → SeparableSpace X →
    (∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
      PrimarinessTransfer 𝕜 (SequenceSum p X) (lp (fun _ : Γ => X) p.val) Γ) ∧
    PrimarinessTransfer 𝕜 (CZeroSum X) C₀(Γ, X) Γ)

/-- Theorem 4.3(i) only (thm:B): WCG ell₁ sums above aleph_1.
The general symmetric-sum clauses (ii),(iii) remain unencoded and unproved. -/
def Theorem_4_3_i (𝕜 : Type*) [RCLike 𝕜]
    (Γ : Type u) (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ → IsWeaklyCompactlyGenerated 𝕜 X →
    (HasUPFP 𝕜 X → HasPFP 𝕜 (EllOneSum Γ X) ∧ HasUPFP 𝕜 (EllOneSum Γ X)) ∧
    (HasPFP 𝕜 X → HasUncountableCofinality Γ → HasPFP 𝕜 (EllOneSum Γ X))

/-- Corollary 4.6: use the type ℝ to index continuum-many coordinates.
The anti-CH and non-uniform alternatives are both retained. -/
def Corollary_4_6 (𝕜 : Type*) [RCLike 𝕜]
    (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] : Prop :=
  (Cardinal.aleph 1 : Cardinal.{0}) < Cardinal.continuum →
  IsWeaklyCompactlyGenerated 𝕜 X →
    (IsUniformlyPrimary 𝕜 (EllOneSum ℕ X) → IsUniformlyPrimary 𝕜 (EllOneSum ℝ X)) ∧
    (IsPrimary 𝕜 (EllOneSum ℕ X) → IsPrimary 𝕜 (EllOneSum ℝ X))

end PFP
