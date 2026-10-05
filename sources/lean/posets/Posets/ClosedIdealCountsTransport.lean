import Posets.ComplementedIdealEmbedding
import Posets.OrdinalInitialRetraction
import Posets.SeparableIdealCases
import Posets.OrdinalIdealTransportLowRank
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-! Ideal counts are invariant under Banach-space isomorphisms, are monotone
under complemented embeddings, and are respectively zero and one in the
finite-dimensional and c₀ cases. -/

noncomputable section
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def nontrivialIdealEmbeddingOfEquiv (e : E ≃L[𝕜] F) :
    NontrivialClosedIdeals 𝕜 (F →L[𝕜] F) ↪ NontrivialClosedIdeals 𝕜 (E →L[𝕜] E) :=
  nontrivialIdealEmbeddingOfRetraction e.symm.toContinuousLinearMap e.toContinuousLinearMap
    (by apply ContinuousLinearMap.ext; intro x; exact e.apply_symm_apply x)

theorem nonempty_nontrivialIdealEquiv (e : E ≃L[𝕜] F) :
    Nonempty (NontrivialClosedIdeals 𝕜 (E →L[𝕜] E) ≃
      NontrivialClosedIdeals 𝕜 (F →L[𝕜] F)) :=
  Function.Embedding.antisymm (nontrivialIdealEmbeddingOfEquiv e.symm)
    (nontrivialIdealEmbeddingOfEquiv e)

def ordinalNontrivialIdealEmbedding {β α : Ordinal.{0}} (h : β ≤ α) :
    NontrivialClosedIdeals 𝕜 (OrdinalSpace 𝕜 β →L[𝕜] OrdinalSpace 𝕜 β) ↪
      NontrivialClosedIdeals 𝕜 (OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α) :=
  nontrivialIdealEmbeddingOfRetraction (ordinalInitialSegmentExtension β α)
    (ordinalInitialSegmentRestriction h) (ordinalInitialSegment_retraction h)

theorem isEmpty_nontrivialIdeals_finitePi (P : Type) [Fintype P] :
    IsEmpty (NontrivialClosedIdeals 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜))) := by
  refine ⟨fun I => ?_⟩
  rcases fullFiniteOperator_closedIdeal_classification ⟨I.val, I.property.1⟩ with h | h
  · exact I.property.2.1 h
  · exact I.property.2.2 h

theorem isEmpty_nontrivialIdeals_finiteCompact (K : Type) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Finite K] :
    IsEmpty (NontrivialClosedIdeals 𝕜 (C(K, 𝕜) →L[𝕜] C(K, 𝕜))) := by
  letI : Fintype K := Fintype.ofFinite K
  letI := isEmpty_nontrivialIdeals_finitePi (𝕜 := 𝕜) K
  let e := (finiteContinuousMapIsometryEquiv (𝕜 := 𝕜) K).toContinuousLinearEquiv
  exact ⟨fun I => isEmptyElim (nontrivialIdealEmbeddingOfEquiv e.symm I)⟩

theorem ordinalBelowOmegaOmega_nontrivialIdealEquivFinOne (α : Ordinal.{0})
    (hlo : Ordinal.omega0 ≤ α) (hhi : α < Ordinal.omega0 ^ Ordinal.omega0) :
    Nonempty (NontrivialClosedIdeals 𝕜 (OrdinalSpace 𝕜 α →L[𝕜] OrdinalSpace 𝕜 α) ≃ Fin 1) := by
  obtain ⟨e⟩ := nonempty_nontrivialIdealEquiv (ordinalBelowOmegaOmegaCZeroEquiv (𝕜 := 𝕜) α hlo hhi)
  exact ⟨e.trans cZeroNontrivialClosedIdealEquivFinOne⟩

theorem not_equiv_fin_of_fin_embedding {A : Type*} {m n : ℕ}
    (h : n < m) (e : Fin m ↪ A) : ¬ Nonempty (A ≃ Fin n) := by
  rintro ⟨f⟩
  have hh := Fintype.card_le_of_injective (f ∘ e) (f.injective.comp e.injective)
  simp only [Fintype.card_fin] at hh
  exact h.not_ge hh

end Posets
