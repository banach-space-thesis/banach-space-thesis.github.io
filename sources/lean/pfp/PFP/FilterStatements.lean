import ThesisCommon.Analysis.FilterConvergenceCriteria
import Mathlib.SetTheory.Cardinal.Aleph

/-! Original Section 6 statements on actual filter-convergence spaces.
The Prop declarations in this file are specifications, not theorem proofs.
The source assumes an infinite index set and a proper filter, and those
hypotheses are retained explicitly. -/
noncomputable section
open Filter Topology
open scoped ENNReal Cardinal
namespace PFP
open ThesisCommon
universe u
variable (𝕜 : Type*) [RCLike 𝕜] (Γ : Type u)

/-- Theorem 6.5, `thm:primary-filter-pfp`, including the UPFP consequence. -/
def Theorem_6_5 [Infinite Γ] (F : Filter Γ) [F.NeBot] (K D : ℝ) : Prop :=
  IsFilterPrimaryForFactorisation (𝕜 := 𝕜) F K D →
    HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 F) (2 * K * D) ∧
    HasUPFP 𝕜 (FilterNullSpace 𝕜 F)

/-- Lemma 6.8, `lem:rosenthal`: finitely additive scalar measures, actual
total variation, full-cardinality selection, and the diagonal atom hypothesis. -/
def Lemma_6_8 [Infinite Γ] : Prop :=
  ∀ μ : Γ → BoundedScalarCharge 𝕜 Γ,
    BoundedScalarCharge.UniformlyBounded μ →
    (∀ γ, μ γ {γ} = 0) → ∀ η : ℝ, 0 < η →
      ∃ A : Set Γ, Cardinal.mk A = Cardinal.mk Γ ∧
        ∀ γ ∈ A, (μ γ).variation A < η

/-- Proposition 6.9, including both the (1,1)-primary-for-factorisation
conclusion and its 2⁺-PFP consequence. -/
def Proposition_6_9 [Infinite Γ] (F : Filter Γ) [F.NeBot] : Prop :=
  IsLargeSetSelfSimilarFilter F →
    IsFilterPrimaryForFactorisation (𝕜 := 𝕜) F 1 1 ∧
      HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 F) 2

/-- The general-cardinal assertion in Example 6.10. Every infinite cardinal
μ ≤ |Γ| is included; no regular-cardinal restriction is added. -/
def Example_6_10_general [Infinite Γ] : Prop :=
  ∀ (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ), μ ≤ Cardinal.mk Γ →
    IsLargeSetSelfSimilarFilter (coSmallFilter (Γ := Γ) μ hμ) ∧
      HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 (coSmallFilter (Γ := Γ) μ hμ)) 2

/-- The cofinite specialisation in Example 6.10, expressed as exact
membership in the actual bounded-sequence space. On a discrete Γ this is
the usual c₀ condition: every positive norm superlevel set is finite. -/
def Example_6_10_cofinite [Infinite Γ] : Prop :=
  coSmallFilter (Γ := Γ) Cardinal.aleph0 le_rfl = Filter.cofinite ∧
    ∀ x : lp (fun _ : Γ => 𝕜) ∞,
      x ∈ filterNullSubmodule 𝕜 (coSmallFilter (Γ := Γ) Cardinal.aleph0 le_rfl) ↔
        ∀ ε : ℝ, 0 < ε → {γ | ε ≤ ‖x γ‖}.Finite

/-- The co-countable specialisation in Example 6.10: precisely the bounded
families having countable support, with the source's cardinal hypothesis. -/
def Example_6_10_cocountable [Infinite Γ] : Prop :=
  Cardinal.aleph 1 ≤ Cardinal.mk Γ →
    ∀ x : lp (fun _ : Γ => 𝕜) ∞,
      x ∈ filterNullSubmodule 𝕜
        (coSmallFilter (Γ := Γ) (Cardinal.aleph 1) (Cardinal.aleph0_le_aleph 1)) ↔
      (Function.support x).Countable

/-- All three assertions of Example 6.10, including both identifications. -/
def Example_6_10 [Infinite Γ] : Prop :=
  Example_6_10_general 𝕜 Γ ∧ Example_6_10_cofinite 𝕜 Γ ∧ Example_6_10_cocountable 𝕜 Γ

/-- The concrete implication displayed in Remark 6.11. -/
def Remark_6_11 [Infinite Γ] (F : Filter Γ) [F.NeBot] : Prop :=
  IsLargeSetSelfSimilarFilter F → HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 F) 2

end PFP
