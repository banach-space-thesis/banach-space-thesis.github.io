import PFP.Preliminaries
import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph

/-! Original targets expressible with the existing concrete space definitions.
These Prop definitions are specifications, not proofs. The remaining source
results are inventoried as pending in source-inventory.json. In particular,
general symmetric sums, James spaces and filter spaces are NOT replaced by
opaque parameters carrying their desired conclusions.
-/
noncomputable section
open scoped ENNReal ZeroAtInfty Cardinal
namespace PFP
open ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Scalar ℓ₁, actual summable families with their sum norm. -/
abbrev ScalarEllOne := lp (fun _ : ℕ => 𝕜) 1
/-- Scalar ℓ∞, all bounded families, with no matrix assumption. -/
abbrev ScalarEllInfinity := lp (fun _ : ℕ => 𝕜) ∞

/-- Theorem 3.11, `th: ell1-case`: ℓ₁ has 2⁺-PFP. -/
def Theorem_3_11 : Prop := HasCPlusPFP 𝕜 (ScalarEllOne 𝕜) 2

/-- Corollary 3.16, including both c₀(ℓ₁) and all 1<p<∞. -/
def Corollary_3_16 : Prop :=
  IsPrimary 𝕜 (CZeroSum (ScalarEllOne 𝕜)) ∧
  ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
    IsPrimary 𝕜 (SequenceSum p (ScalarEllOne 𝕜))

/-- Theorem 3.21, `th: UPFP_l_infty`: ℓ∞ has 2⁺-PFP. -/
def Theorem_3_21 : Prop := HasCPlusPFP 𝕜 (ScalarEllInfinity 𝕜) 2

/-- Corollary 3.27: c₀(ℓ∞) is primary. -/
def Corollary_3_27 : Prop := IsPrimary 𝕜 (CZeroSum (ScalarEllInfinity 𝕜))

/-- Corollary 4.7, `cor:intro-C01`: under ¬CH the dual of C[0,1] is primary.
The cardinal inequality is in Cardinal.{0}; the dual is the bounded dual. -/
def Corollary_4_7 : Prop :=
  (Cardinal.aleph 1 : Cardinal.{0}) < Cardinal.continuum →
    IsPrimary 𝕜 (IntervalContinuous 𝕜 →L[𝕜] 𝕜)

/-- Corollary 4.10(i), including its primariness conclusion. Ordinal and
index universes are arbitrary and independent; p=1 is included. -/
def Corollary_4_10_i (Γ : Type u) (α : Ordinal.{v}) : Prop :=
  Cardinal.aleph 1 < Cardinal.mk Γ →
  ∀ p : BanachExponent, p.val ≠ ∞ →
    HasUPFP 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p.val) ∧
    IsPrimary 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p.val)

/-- Corollary 4.10(ii), with c₀ included. The discrete topology is part of
the definition of c₀(Γ), not an additional condition on the index set. -/
def Corollary_4_10_ii (Γ : Type u) [TopologicalSpace Γ] [DiscreteTopology Γ]
    (α : Ordinal.{v}) : Prop :=
  α < (Cardinal.aleph 1).ord → Cardinal.aleph0 < Cardinal.mk Γ →
    (∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
      HasUPFP 𝕜 (lp (fun _ : Γ => OrdinalContinuous 𝕜 α) p.val)) ∧
    HasUPFP 𝕜 C₀(Γ, OrdinalContinuous 𝕜 α)

/-- X_n = B(ℓp^n), with its actual operator norm. -/
abbrev MatrixBlock (p : BanachExponent) (n : ℕ) :=
  lp (fun _ : Fin n => 𝕜) p.val →L[𝕜] lp (fun _ : Fin n => 𝕜) p.val

/-- M_p = the ℓ∞ sum of B(ℓp^n), n=1,2,... . The +1 accounts for Lean's
zero-based natural numbers and avoids inserting a spurious first block. -/
abbrev MatrixSum (p : BanachExponent) := lp (fun n : ℕ => MatrixBlock 𝕜 p (n + 1)) ∞

/-- Theorem 5.14, `thm:MpUPFP`, with the numerical constant 8. -/
def Theorem_5_14 : Prop := ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
  HasCPFP 𝕜 (MatrixSum 𝕜 p) 8

/-- Theorem 5.15, `thm:BlpUPFP`: B(ℓp) has UPFP for every 1<p<∞. -/
def Theorem_5_15 : Prop := ∀ p : BanachExponent, 1 < p.val → p.val ≠ ∞ →
  HasUPFP 𝕜 (SequenceSum p 𝕜 →L[𝕜] SequenceSum p 𝕜)

end PFP
