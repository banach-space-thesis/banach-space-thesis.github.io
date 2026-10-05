import ThesisCommon.Analysis.SequenceSpaces
import ThesisCommon.Analysis.SetMappingDefinitions

/-! Exact supporting statements 4.19--4.23 from the uncountable direct-sum
section. Declarations with capitalised names are Prop specifications. The
explicit theorems `lemma_4_20` and `remark_4_23` below supply numbered proofs. -/
noncomputable section
open scoped Cardinal ENNReal ZeroAtInfty
namespace PFP
open ThesisCommon
universe u v

/-- Lemma 4.19, `lem:countable-blocks-lp-c0`: both finite-p and c₀ assertions,
including finite nonempty blocks. The topology on the coordinate type is discrete. -/
def Lemma_4_19 (𝕜 : Type*) [RCLike 𝕜]
    (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (Δ : Type u) [Nonempty Δ] [Countable Δ]
    [TopologicalSpace Δ] [DiscreteTopology Δ] : Prop :=
  (∀ p : BanachExponent, p.val ≠ ∞ →
    Nonempty (lp (fun _ : Δ => SequenceSum p Y) p.val ≃ₗᵢ[𝕜] SequenceSum p Y)) ∧
    Nonempty (C₀(Δ, CZeroSum Y) ≃ₗᵢ[𝕜] CZeroSum Y)

/-- Lemma 4.20, `lem:cofinal-pigeon`: a countable union covering the specified
set has a full-cardinality member. κ may be singular; only cf(κ)>aleph-zero is
required. The union equality also ensures that every member is a subset of S. -/
def Lemma_4_20 (Γ : Type u) : Prop :=
  ∀ κ : Cardinal.{u}, Cardinal.aleph0 ≤ κ → Cardinal.aleph0 < κ.ord.cof →
    ∀ S : Set Γ, Cardinal.mk S = κ → ∀ A : ℕ → Set Γ,
      S = ⋃ n, A n → ∃ n, Cardinal.mk (A n) = κ

/-- Proposition 4.21, `prop:hajnal`: the complete stated Hajnal theorem.
The value-size bound is strict (<λ), λ is strictly below κ, and κ need not be
regular. The domain is the actual initial ordinal representing κ. -/
def Proposition_4_21 : Prop :=
  ∀ κ μ : Cardinal.{u}, Cardinal.aleph0 ≤ κ → μ < κ →
    ∀ F : κ.ord.toType → Set κ.ord.toType,
      IsSetMapping F → (∀ α, Cardinal.mk (F α) < μ) →
        ∃ H : Set κ.ord.toType, Cardinal.mk H = κ ∧ IsSetMappingFree F H

/-- Proposition 4.22, `prop:two-sided-countable-free`: both values and inverse
incidence fibres must be countable. This includes every uncountable singular
cardinal; no cf(κ)>aleph-zero condition is inserted. -/
def Proposition_4_22 : Prop :=
  ∀ κ : Cardinal.{u}, Cardinal.aleph0 < κ →
    ∀ F : κ.ord.toType → Set κ.ord.toType,
      IsSetMapping F → HasTwoSidedCountableValues F →
        ∃ H : Set κ.ord.toType, Cardinal.mk H = κ ∧ IsSetMappingFree F H

/-- The concrete mathematical assertion in Remark 4.23,
`rem:omega-one-obstruction`, with exactly the printed predecessor mapping. -/
def Remark_4_23 : Prop :=
  Cardinal.mk OmegaOneIndex.{u} = Cardinal.aleph 1 ∧
    IsSetMapping omegaOnePredecessors.{u} ∧
      (∀ α : OmegaOneIndex.{u}, (omegaOnePredecessors α).Countable) ∧
        ∀ H : Set OmegaOneIndex.{u}, IsSetMappingFree omegaOnePredecessors H → H.Subsingleton

theorem lemma_4_20 (Γ : Type u) : Lemma_4_20 Γ := by
  intro κ hκ hcof S hS A hA
  exact countable_union_cofinal_pigeonhole hκ hcof S hS A hA

theorem remark_4_23 : Remark_4_23.{u} :=
  ⟨mk_omegaOneIndex, omegaOnePredecessors_isSetMapping,
    omegaOnePredecessors_countable, omegaOnePredecessors_free_subsingleton⟩

end PFP
