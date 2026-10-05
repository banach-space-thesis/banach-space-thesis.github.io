import ThesisCommon.Analysis.CountableCoordinateSupport

/-! Checked ℓp/c₀ cases of §4's support lemmas. General symmetric sums and
the WCG hypothesis still require separate proofs, not extra assumed fields. -/
namespace PFP
open scoped ENNReal ZeroAtInfty
open ThesisCommon TopologicalSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Γ X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lemma_4_12_lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hfin : p ≠ ∞)
    (x : lp (fun _ : Γ => X) p) : (Function.support x).Countable :=
  lp_countable_support (ne_of_gt (zero_lt_one.trans_le Fact.out)) hfin x

theorem lemma_4_12_cZero [TopologicalSpace Γ] [DiscreteTopology Γ]
    (x : C₀(Γ, X)) : (Function.support x).Countable := cZero_countable_support x

include 𝕜 in
theorem lemma_4_13_lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hfin : p ≠ ∞)
    {s : Set (lp (fun _ : Γ => X) p)} (hs : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ x ∈ s, Function.support x ⊆ Δ :=
  lp_separable_countable_support (𝕜 := 𝕜) hfin hs

include 𝕜 in
theorem lemma_4_13_cZero [TopologicalSpace Γ] [DiscreteTopology Γ]
    {s : Set C₀(Γ, X)} (hs : IsSeparable s) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ x ∈ s, Function.support x ⊆ Δ :=
  cZero_separable_countable_support (𝕜 := 𝕜) hs
end PFP
